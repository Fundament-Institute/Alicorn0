local lpeg = require "lpeg"
local P, C, Cg, Cc, Cmt, Ct, Cb, Cp, Cf, Cs, S, V, R =
	lpeg.P, lpeg.C, lpeg.Cg, lpeg.Cc, lpeg.Cmt, lpeg.Ct, lpeg.Cb, lpeg.Cp, lpeg.Cf, lpeg.Cs, lpeg.S, lpeg.V, lpeg.R

-- SLN
-- expressions, atoms, lists
-- documentation for the SLN: https://scopes.readthedocs.io/en/latest/dataformat/
-- a python SLN parser: https://github.com/salotz/python-sln/blob/master/src/sln/parser.py

---@class Anchor
---@field line integer
---@field char integer
---@field sourceid string
local Anchor = {}

local anchor_mt = {
	__lt = function(fst, snd)
		return snd.line > fst.line or (snd.line == fst.line and snd.char > fst.char)
	end,
	__le = function(fst, snd)
		return fst < snd or fst == snd
	end,
	__eq = function(fst, snd)
		return (snd.line == fst.line and snd.char == fst.char)
	end,
	__tostring = function(self)
		return "in file " .. self.sourceid .. ", line " .. self.line .. " character " .. self.char
	end,
	__index = Anchor,
}

local function element(kind, pattern)
	return Ct(Cg(V "textpos", "anchor") * Cg(Cc(kind), "kind") * pattern)
end

local function symbol(value)
	return element("symbol", Cg(value, "str"))
end

local function space_tokens(pattern)
	local token_spacer = S "\t " ^ 0
	return pattern * token_spacer
end

-- Incrementally Fold Repetitions at Match Time
-- incrementally fold the stack into actual tables to prevent stack overflows
local function IFRmt(pattern, numtimes)
	if _VERSION == "Lua 5.1" then
		table.unpack = unpack
	end

	local repetition

	if numtimes == 0 then
		repetition = Cg(Ct(pattern ^ -1), "IFRmt_acc")
			* Cg(
					Cmt(Cb("IFRmt_acc") * pattern, function(_, _, prev, newval)
						table.insert(prev, newval)
						return true, prev
					end),
					"IFRmt_acc"
				)
				^ 0
	elseif numtimes > 0 then
		repetition = Cg(Ct(pattern), "IFRmt_acc")
			* Cg(
					Cmt(Cb("IFRmt_acc") * pattern, function(_, _, prev, newval)
						table.insert(prev, newval)
						return true, prev
					end),
					"IFRmt_acc"
				)
				^ (numtimes - 1)
	end

	-- / func can return multiple values which become multiple distinct captures
	-- which prevents needing to change the behavior of list
	repetition = repetition * (Cb("IFRmt_acc") / function(vals)
		return table.unpack(vals)
	end)

	return repetition
end

local function list(pattern)
	return (V "textpos" * Ct(pattern) * V "textpos")
		/ function(anchor, elements, endpos)
			return {
				anchor = anchor,
				elements = elements,
				endpos = endpos,
				kind = "list",
			}
		end
end

---@class Literal
---@field anchor Anchor
---@field kind LiteralKind
---@field literaltype LiteralType?
---@field val number | table | nil

---@alias LiteralKind "list" | "symbol" | "string" | "literal"
---@alias LiteralType "u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64"  | "f32" | "f64" | "bytes" | "unit"

local function update_ffp(name, patt)
	-- stage the error
	-- if the pattern matches, erase the stage
	-- if the pattern doesn't match, the stage persists

	-- should there be some mechanism to not include the results of emptylines? ignore them?

	return patt
		+ (
			Cmt(lpeg.Carg(2) * V "textpos", function(_, _, ctx, position)
				if ctx.position then
					if ctx.position == position then
						local acc = true
						for i, v in ipairs(ctx.expected) do
							acc = acc and not (v == name)
						end
						if acc then
							table.insert(ctx.expected, name)
						end
					elseif ctx.position < position then
						ctx.position = position
						ctx.expected = { name }
					end
				else
					ctx.position = position
					ctx.expected = { name }
				end

				return false
			end) * P(1) -- this segment always fails, so P(1) is to assure lpeg that this isn't an empty loop
		)
end

local function clear_ffp()
	return lpeg.Carg(2) / function(ctx)
		ctx.position = nil
		ctx.expected = nil
	end
end

local function create_literal(anchor, elements)
	local val = {
		anchor = anchor,
		kind = "literal",
		literaltype = "bytes",
		val = {},
	}

	for char in elements:gmatch "." do
		table.insert(val.val, string.byte(char))
	end

	return val
end

local function erase(pattern)
	return pattern / {}
end

---@param line integer
---@param char integer
---@param sourceid string
---@return Anchor
local function create_anchor(line, char, sourceid)
	local newanchor = {
		line = line,
		char = char,
		sourceid = sourceid,
	}
	setmetatable(newanchor, anchor_mt)
	return newanchor
end

local grammar = P {
	"ast",
	-- initializes empty capture groups at the start, remember to update when tracking new things!
	foreward = Cg(Cc(0), "indent_level"),

	ast = V "foreward" * list(
		IFRmt(V "empty_line" + ((V "newline" + V "filestart") * V "baselevel" * V "naked_list"), 0)
	) * V "eof" * clear_ffp(),

	-- either match the newline or match the beginning of the file
	filestart = Cmt(P "", function(_, mypos)
		return mypos == 1
	end),
	eof = P(-1),

	newline = (P "\r" ^ 0 * P "\n") * Cmt(lpeg.Carg(1), function(_, position, table)
		if not (table.positions[#table.positions].pos == position) then
			if table.positions[#table.positions].pos < position then
				table.positions[#table.positions + 1] =
					{ pos = position, line = table.positions[#table.positions].line + 1 }
			end
		end

		return true
	end),
	empty_line = V "newline" * S "\t " ^ 0 * #(V "newline" + V "eof"),

	textpos = Cmt(lpeg.Carg(1), function(_, position, linectx)
		-- assert(position > table.positions[#table.positions].pos)
		local line_index = #linectx.positions

		while (position < linectx.positions[line_index].pos) and (line_index > 0) do
			line_index = line_index - 1
		end
		local simple = create_anchor(
			linectx.positions[line_index].line,
			position - linectx.positions[line_index].pos + 1,
			linectx.sourceid
		)
		return true, simple
	end),

	count_tabs = update_ffp(
		"spaces should not be interspersed in indentation",
		Cmt(V "textpos" * C(S "\t " ^ 0), function(_, _, anchor, indentstring)
			if string.find(indentstring, " ") then
				return false
			end
			return true, string.len(indentstring)
		end)
	),

	-- use indent and dedent to control the expected indentation level of a context
	-- samedent is the token that is consumed on a newline

	indent = Cg(Cb("indent_level") / function(level)
		return math.max(0, level + 1)
	end, "indent_level"),
	dedent = Cg(Cb("indent_level") / function(level)
		return math.max(0, level - 1)
	end, "indent_level"),

	baselevel = update_ffp(
		"no indentation",
		Cmt(Cb("indent_level") * V "count_tabs", function(_, _, prev_indent, tabscount)
			return (prev_indent == 0) and (tabscount == 0)
		end)
	),

	blockline = update_ffp(
		"block level newline",
		V "newline"
			* Cmt(Cb("indent_level") * V "count_tabs", function(_, _, prev_indent, tabscount)
				return tabscount == prev_indent
			end)
	),

	superior_indent = update_ffp(
		"dedent",
		V "newline"
			* Cmt(Cb("indent_level") * V "count_tabs", function(_, _, prev_indent, tabscount)
				return tabscount <= prev_indent
			end)
	),

	subordinate_indent = update_ffp(
		"subordinate indent",
		V "newline"
			* Cmt(Cb("indent_level") * V "count_tabs", function(_, _, prev_indent, tabscount)
				local normalized_tabs = string.rep("\t", tabscount - prev_indent - 1)
				return tabscount > prev_indent, normalized_tabs
			end)
	),

	-- probably works but it doesn't have complex tests
	splice = P "${" * V "naked_list" * P "}" + P "$" * V "symbol",
	escape_chars = Cs(P [[\\]] / [[\]] + P [[\"]] / [["]] + P [[\n]] / "\n" + P [[\r]] / "\r" + P [[\t]] / "\t"),
	unicode_escape = P "\\u" * (V "hex_digit") ^ 4 ^ -4,

	string_literal = V "textpos" * Cs(
		(V "escape_chars" + V "unicode_escape" + C(1 - (S [["\]] + V "newline" + V "splice"))) ^ 1
	) / create_literal,
	string = element(
		"string",
		P '"'
			* Cg(Ct((V "string_literal" + V "splice") ^ 0), "elements")
			* update_ffp('"', P '"')
			* Cg(V "textpos", "endpos")
	),

	longstring_literal = V "textpos" * Cs(
		((V "subordinate_indent" + V "empty_line") + C((V "unicode_escape" + (1 - (V "newline" + V "splice"))))) ^ 1
	) / create_literal,
	longstring = element("string", P '""""' * Cg(Ct((V "longstring_literal" + V "splice") ^ 0), "elements")),

	comment_body = C((1 - V "newline") ^ 1),
	line_comment = update_ffp("comment", element("comment", (P "#" * Cg(V "comment_body", "val")))),
	comment = update_ffp(
		"comment",
		element("comment", (P "#" * Cg(Cs((V "subordinate_indent" + V "comment_body" + V "empty_line") ^ 0), "val")))
	),

	tokens = update_ffp(
		"token",
		space_tokens(
			V "line_comment"
				+ V "function_call"
				+ V "paren_list"
				+ V "longstring"
				+ V "string"
				+ V "number"
				+ V "symbol"
		)
	),

	semicolon = update_ffp(";", space_tokens(P ";") * (V "line_comment" * #(V "newline" + V "eof")) ^ -1),
	naked_list = V "empty_line"
		+ (V "tokens" * V "line_comment" ^ -1 * #(V "superior_indent" + V "eof"))
		+ (V "comment") --
		+ (list(V "tokens" ^ 0 * V "semicolon") * #(V "blockline" + V "eof"))
		+ list(
			(((list(V "tokens" ^ 1 * V "semicolon") + V "semicolon") ^ 1 * V "tokens" ^ 0) + V "tokens" ^ 1)
				* V "indent"
				* IFRmt(((V "blockline" * V "naked_list") + V "empty_line"), 0)
		),

	-- PARENTHETICAL LIST BEHAVIOR
	paren_spacers = (
		erase(V "subordinate_indent") --
		+ (V "line_comment" * #(V "newline" + V "eof"))
		+ V "empty_line"
		+ S "\t " ^ 1
	) ^ 0,
	paren_tokens = update_ffp(
		"tokens",
		(
			(P [[\]] * V "paren_spacers" * V "naked_list") -- \ escape char enters naked list mode from inside a paren list. there's probably an edge case here, indentation is going to be wacky
			+ V "tokens"
		) * V "paren_spacers"
	),

	psemicolon = update_ffp(";", P ";" * V "paren_spacers"),
	semicolon_body = list(IFRmt(V "paren_tokens", 1) * V "psemicolon") ^ 1 * IFRmt(V "paren_tokens", 0),

	comma = update_ffp('","', P "," * V "paren_spacers"),
	comma_paren_body = ((list(IFRmt(V "paren_tokens", 2)) + V "paren_tokens") * V "comma") ^ 1
		* (list(IFRmt(V "paren_tokens", 2)) + V "paren_tokens"),

	open_brace = Cg(C(P "("), "bracetype")
		+ (Cg(C(P "["), "bracetype") * symbol(Cc("braced_list")))
		+ (Cg(C(P "{"), "bracetype") * symbol(Cc("curly-list"))),
	close_brace = update_ffp(
		"matching close brace",
		Cmt(Cb("bracetype") * C(S "])}"), function(_, _, bracetype, brace)
			local matches = {
				["("] = ")",
				["["] = "]",
				["{"] = "}",
			}
			return matches[bracetype] == brace
		end)
	),
	paren_list = list(
		V "open_brace"
			* V "paren_spacers"
			* (V "comma_paren_body" + V "semicolon_body" + V "paren_tokens" ^ 1) ^ -1
			* V "close_brace"
	),

	function_call = V "symbol" * Ct(
		list(
			P "("
				* V "paren_spacers"
				* (V "comma_paren_body" + V "paren_tokens") ^ -1
				* update_ffp("close brace", P ")")
		) ^ 1
	) / function(symbol, argcalls)
		local acc = {}

		acc = table.remove(argcalls, 1)
		table.insert(acc.elements, 1, symbol)
		acc.anchor = symbol.anchor

		for _, v in ipairs(argcalls) do
			table.insert(v.elements, 1, acc)
			v.anchor = acc.anchor
			acc = v
		end

		return acc
	end,

	-- numbers are limited, they are not bignums, they are standard lua numbers. scopes shares the problem of files not having arbitrary precision
	-- so it probably doesn't matter.
	number = element("literal", Cg((V "float_special" + V "hex" + V "big_e") / tonumber, "val") * V "types"),
	types = Cg(
		(P ":" * C((S "iu" * (P "8" + P "16" + P "32" + P "64")) + (P "f" * (P "32" + P "64")))) + P "" / "f64",
		"literaltype"
	),
	digit = R("09") ^ 1,
	hex_digit = (V "digit" + R "AF" + R "af") ^ 1,
	decimal = S "-+" ^ -1 * V "digit" * (P "." * V "digit") ^ -1,
	hex = S "+-" ^ -1 * P "0x" * V "hex_digit" * (P "." * V "hex_digit") ^ -1,
	big_e = V "decimal" * (P "e" * V "decimal") ^ -1,
	float_special = P "+inf" + P "-inf" + P "nan",

	symbol = symbol((1 - (S "\\#()[]{};,\t \n\r")) ^ 1),
}

local function span_error(position, subject, msg)
	local lines = {}
	for line in subject:gmatch("([^\n\r]*)\r*\n") do
		table.insert(lines, line)
	end
	local line = lines[position.line] or ""

	local _, tabnum = line:gsub("\t", "")
	local caret_wsp = ("\t"):rep(tabnum) .. (" "):rep(position.char - (1 + tabnum))
	local linenum_wsp = (" "):rep(string.len(position.line))

	local span = string.format(
		[[
error: %s
--> %s:%i:%i
%s |
%i |%s
%s |%s^
	]],
		msg,
		position.sourceid,
		position.line,
		position.char,
		linenum_wsp,
		position.line,
		line,
		linenum_wsp,
		caret_wsp
	)

	return span
end

---@class FormatList
---@field anchor Anchor
---@field endpos Anchor
---@field kind LiteralKind
---@field elements table[]

---@param input string
---@param filename string
---@return FormatList?
local function parse(input, filename)
	assert(filename)

	if not (string.len(input) > 0) then
		print("empty file")
		return nil
	end

	local newlinetable = {
		sourceid = filename,
		positions = { {
			pos = 1,
			line = 1,
		} },
	}
	local furthest_forward = { position = nil }
	local ast = lpeg.match(grammar, input, 1, newlinetable, furthest_forward)

	if furthest_forward.position then
		local expected = "{"
		for i, v in ipairs(furthest_forward.expected) do
			expected = expected .. v .. ", "
		end
		expected = expected .. "}"

		assert(false, span_error(furthest_forward.position, input, "expected " .. expected))
	end

	return ast
end

return { parse = parse, anchor_mt = anchor_mt }
