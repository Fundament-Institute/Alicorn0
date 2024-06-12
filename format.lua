local lpeg = require "lpeg"
local P, C, Cg, Cc, Cmt, Ct, Cb, Cp, Cf, Cs, S, V, R =
	lpeg.P, lpeg.C, lpeg.Cg, lpeg.Cc, lpeg.Cmt, lpeg.Ct, lpeg.Cb, lpeg.Cp, lpeg.Cf, lpeg.Cs, lpeg.S, lpeg.V, lpeg.R

-- SLN
-- expressions, atoms, lists
-- documentation for the SLN: https://scopes.readthedocs.io/en/latest/dataformat/
-- a python SLN parser: https://github.com/salotz/python-sln/blob/master/src/sln/parser.py

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

local function list(pattern)
	return element("list", Cg(Ct(space_tokens(pattern)), "elements") * Cg(V "textpos", "endpos"))
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

local function create_anchor(line, char, sourceid)
	local newanchor = {
		line = line,
		char = char,
		sourceid = sourceid,
	}
	setmetatable(newanchor, anchor_mt)
	return newanchor
end

local function delimsep(pattern, delim)
	return (pattern * delim) ^ 0 * pattern
end

local grammar = P {
	"ast",
	-- initializes empty capture groups at the start, remember to update when tracking new things!
	foreward = Cg(Cc(0), "indent_level"),

	ast = V "foreward" * list(
		((V "empty_line" + (((V "newline") + V "filestart") * V "samedent" * V "naked_list")) ^ 0)
			* V "furthest_forward" ^ -1
			* V "eof"
	),

	-- either match the newline or match the beginning of the file
	filestart = Cmt(P "", function(_, mypos)
		return mypos == 1
	end),
	eof = P(-1),

	newline = (P "\r" ^ 0 * P "\n") * lpeg.Carg(1) * Cp() / function(table, position)
		table.positions[#table.positions + 1] = { pos = position, line = table.positions[#table.positions].line + 1 }
	end,
	empty_line = V "newline" * S "\t " ^ 0 * #(V "newline" + V "eof"),

	textpos = lpeg.Carg(1) * Cp() / function(table, position)
		local simple = create_anchor(
			table.positions[#table.positions].line,
			position - table.positions[#table.positions].pos + 1,
			table.sourceid
		)
		return simple
	end,

	count_tabs = Cmt(V "textpos" * C(S "\t " ^ 0), function(_, _, anchor, indentstring)
		if string.find(indentstring, " ") then
			assert(false, "error at " .. tostring(anchor) .. ": tabs and spaces must not be interspersed")
		end
		return true, string.len(indentstring)
	end),

	-- use indent and dedent to control the expected indentation level of a context
	-- samedent is the token that is consumed on a newline

	indent = Cg(Cb("indent_level") / function(level)
		return math.max(0, level + 1)
	end, "indent_level"),
	dedent = Cg(Cb("indent_level") / function(level)
		return math.max(0, level - 1)
	end, "indent_level"),

	samedent = Cmt(Cb("indent_level") * V "count_tabs", function(_, _, prev_indent, tabscount)
		return tabscount == prev_indent
	end),

	superior_indent = Cmt(Cb("indent_level") * V "count_tabs", function(_, _, prev_indent, tabscount)
		return tabscount <= prev_indent
	end),

	subordinate_indent = Cmt(Cb("indent_level") * V "count_tabs", function(_, _, prev_indent, tabscount)
		local normalized_tabs = string.rep("\t", tabscount - prev_indent - 1)
		return tabscount > prev_indent, normalized_tabs
	end),

	-- probably works but it doesn't have complex tests
	splice = P "${" * V "naked_list" * P "}" + P "$" * V "symbol",
	escape_chars = Cs(P [[\\]] / [[\]] + P [[\"]] / [["]] + P [[\n]] / "\n" + P [[\r]] / "\r" + P [[\t]] / "\t"),
	unicode_escape = P "\\u" * (V "hex_digit") ^ 4 ^ -4,

	string_literal = V "textpos" * Cs(
		(V "escape_chars" + V "unicode_escape" + C(1 - (S [["\]] + V "newline" + V "splice"))) ^ 1
	) / create_literal,
	string = element(
		"string",
		P '"' * Cg(Ct((V "string_literal" + V "splice") ^ 0), "elements") * P '"' * Cg(V "textpos", "endpos")
	),

	longstring_literal = V "textpos" * Cs(
		(
			((V "newline" * V "subordinate_indent") + V "empty_line")
			+ C((V "unicode_escape" + (1 - (V "newline" + V "splice"))))
		) ^ 1
	) / create_literal,
	longstring = element("string", P '""""' * Cg(Ct((V "longstring_literal" + V "splice") ^ 0), "elements")),

	comment_body = C((1 - V "newline") ^ 1),
	line_comment = element("comment", (P "#" * Cg(V "comment_body", "val"))),
	comment = element(
		"comment",
		(P "#" * Cg(Cs(((V "newline" * V "subordinate_indent") + V "comment_body" + V "empty_line") ^ 0), "val"))
	),

	tokens = space_tokens(
		V "line_comment" + V "function_call" + V "paren_list" + V "longstring" + V "string" + V "number" + V "symbol"
	),

	semicolon = space_tokens(P ";") * (V "line_comment" * #V "newline") ^ -1,
	comma = space_tokens(P ",") * (V "line_comment" * #V "newline") ^ -1,

	solo_token = V "tokens" * V "line_comment" ^ -1,

	naked_list = V "empty_line"
		+ (V "solo_token" * #((V "newline" * V "superior_indent") + V "eof"))
		+ (V "comment")
		+ (list(V "tokens" ^ 0 * V "semicolon") * #((V "newline" * V "samedent") + V "eof"))
		+ list(
			(((list(V "tokens" ^ 1 * V "semicolon") + V "semicolon") ^ 1 * V "tokens" ^ 0) + V "tokens" ^ 1)
				* V "indent"
				* (V "newline" * V "samedent" * V "naked_list") ^ 0
		),

	-- PARENTHETICAL LIST BEHAVIOR
	paren_tokens = (
		(V "newline" * erase(V "subordinate_indent"))
		+ V "empty_line"
		+ S "\t " ^ 1
		+ (space_tokens(P [[\]]) * V "naked_list") -- \ escape char enters naked list mode from inside a paren list. there's probably an edge case here, indentation is going to be wacky
		+ V "tokens"
	),

	semicolon_body = list(V "paren_tokens" ^ 1 * V "semicolon") ^ 1 * V "paren_tokens" ^ 0,

	comma_paren_body = ((list(V "paren_tokens" ^ 2) + V "paren_tokens") * V "comma") ^ 1
		* (list(V "paren_tokens" ^ 2) + V "paren_tokens"),

	open_brace = Cg(C(P "("), "bracetype")
		+ (Cg(C(P "["), "bracetype") * symbol(Cc("braced_list")))
		+ (Cg(C(P "{"), "bracetype") * symbol(Cc("curly-list"))),
	close_brace = Cmt(Cb("bracetype") * C(S "])}"), function(_, _, bracetype, brace)
		local matches = {
			["("] = ")",
			["["] = "]",
			["{"] = "}",
		}
		return matches[bracetype] == brace
	end),
	paren_list = list(
		V "open_brace" * (V "comma_paren_body" + V "semicolon_body" + V "paren_tokens" ^ 1) * V "close_brace"
	),

	function_call = V "symbol"
		* Ct(list(P "(" * (V "comma_paren_body" + V "solo_token") ^ -1 * P ")") ^ 1)
		/ function(symbol, argcalls)
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

	furthest_forward = lpeg.Carg(2) * V "textpos" * P(1) ^ 1 / function(table, position)
		if table.position then
			if table.position < position then
				table.position = position
			end
		else
			table.position = position
		end
	end,
}

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

	assert(ast, "completely failed to parse format")

	if furthest_forward.position then
		assert(false, "errors " .. tostring(furthest_forward.position))
	end

	return ast
end

return { parse = parse }
