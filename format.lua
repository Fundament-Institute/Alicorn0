local lpeg = require "lpeg"
local P, C, Cg, Cmt, Ct, Cb, Cp, Cf, S, V, R = lpeg.P, lpeg.C, lpeg.Cg,
                                               lpeg.Cmt, lpeg.Ct, lpeg.Cb,
                                               lpeg.Cp, lpeg.Cf, lpeg.S, lpeg.V,
                                               lpeg.R

-- SLN
-- expressions, atoms, lists
-- documentation for the SLN: https://scopes.readthedocs.io/en/latest/dataformat/
-- a python SLN parser: https://github.com/salotz/python-sln/blob/master/src/sln/parser.py

local anchor_mt = {
	__tostring = function(self)
		return
			"in file" .. self.sourceid .. ", line " .. self.line .. " character " ..
				self.char
	end
}

local function element(kind, pattern)
	return Ct(V "anchor" * Cg(P "" / kind, "kind") * pattern)
end

local function space_tokens(pattern)
	local token_spacer = S "\t " ^ 0
	return pattern * token_spacer
end

local function list(pattern)
	return element("list", Cg(Ct(space_tokens(pattern)), "elements") * V "endpos")
end

local function replace_escape(data)
	if data == [[\\]] then
		return [[\]]
	elseif data == [[\"]] then
		return [["]]
	elseif data == [[\n]] then
		return "\n"
	elseif data == [[\r]] then
		return "\r"
	elseif data == [[\t]] then
		return "\t"
	end
end

local function string_concat(a, b)
	if a and (not b) then
		return a
	elseif b and (not a) then
		return b
	else
		return a .. " " .. b
	end
end

local grammar = P {
	"ast",
	ast = V "foreward" * V "file",

	wsp = lpeg.S "\t\n\r ",
	foreward = Cg(P "" / function(_) return {0} end, "indent_level") *
		Cg(P "" / function() return {line_num = 1, line_pos = 0} end, "newline_pos"),

	-- every time there's a newline, get it's position. construct a named group with the position
	-- of the latest (numbered) newline
	newline = Cg(Cmt(Cb("newline_pos") * P"\r"^0 * P"\n" * Cp(),
	                 function(body, position, prev_pos)
		local construct = {line_num = prev_pos["line_num"] + 1, line_pos = position}
		return true, construct
	end), "newline_pos"),
	-- either match the newline or match the beginning of the file

	filestart = Cg(Cmt(Cp(), function(body, position, mypos)
		if mypos == 1 then
			return mypos == 1, {line_num = 0, line_pos = 0}
		else
			return mypos == 1
		end
	end), "newline_pos"),

	-- every time there's a newline, get it's position, and construct a named group
	-- subtract the position of the newline and use it as a comparison point
	textpos = Cp() * Cb("newline_pos") * lpeg.Carg(1) /
		function(new_pos, old_pos, filename)
			local anchor = {
				sourceid = filename,
				line = old_pos["line_num"],
				char = new_pos - old_pos["line_pos"]
			}
			setmetatable(anchor, anchor_mt)

			return anchor
		end,

	anchor = Cg(V "textpos", "anchor"),
	endpos = Cg(V "textpos", "endpos"),

	count_tabs = Cmt(V "textpos" * C(S "\t " ^ 1),
	                 function(body, position, anchor, indentstring)
		-- only tabs are allowed
		-- tabs and spaces must not be interleaved - tabs must happen before spaces.
		-- TODO: make nice errors in here

		local numtabs = 0

		for i = 1, #indentstring do
			local char = indentstring:sub(i, i)
			local lookbehind_char = indentstring:sub(i - 1, i - 1)

			if (char == "\t") and (lookbehind_char == " ") then
				print("error at ", anchor, ": tabs and spaces must not be interspersed")
				return false
			elseif char == "\t" then
				numtabs = numtabs + 1
			end
		end

		return true, numtabs

	end),

	-- an indented block which may have indents and dedents, so long as those indents
	-- are subordinate to the initial indent
	subordinate_indent = V "newline" * Cmt(Cb("indent_level") * V "count_tabs",
	                                       function(body, position, prev_indent,
	                                                this_indent)
		return this_indent > prev_indent[#prev_indent]
	end),

	-- for the time being, accurate recording/reporting of indentation level (indentation level - parent indentation) is unsupported.
	contiguous_body = (1 - S "\r\n") ^ 0,
	subordinate_body = C(V "contiguous_body") *
		(C(V "subordinate_indent" * V "contiguous_body") + C(V "wsp" ^ 1)) ^ 0,
	comment = element("comment", Cg(
		                  P "#" * lpeg.Cf(V "subordinate_body", string_concat), "val")),
	-- TODO automatically convert body to schema bytes variant
	longstring = element("string", Cg(
		                     lpeg.Cf((P [[""""]] * V "subordinate_body"),
		                             string_concat), "val")),

	-- numbers are limited, they are not bignums, they are standard lua numbers. scopes shares the problem of files not having arbitrary precision
	-- so it probably doesn't matter.
	number = element("literal", Cg(
		                 (V "float_special" + V "hex" + V "big_e") / tonumber, "val") *
		                 V "types"),
	types = Cg((P ":" *
		           C(
			           (S "iu" * (P "8" + P "16" + P "32" + P "64")) +
				           (P "f" * (P "32" + P "64")))) + P "" / "f64", "literaltype"),
	digit = R("09") ^ 1,
	hex_digit = (V "digit" + R "AF" + R "af") ^ 1,
	decimal = S "-+" ^ 0 * V "digit" * (P "." * V "digit") ^ 0,
	hex = S "+-" ^ 0 * P "0x" * V "hex_digit" * (P "." * V "hex_digit") ^ 0,
	big_e = V "decimal" * (P "e" * V "decimal") ^ 0,
	float_special = P "+inf" + P "-inf" + P "nan",

	symbol = element("symbol", Cg((1 - (S "#;()[]{}," + V "wsp")) ^ 1, "str")),
	comma = element("symbol", Cg(P ",", "str")),

	-- probably works but it doesn't have complex tests
	splice = P "${" * V "naked_list" * P "}",
	backslashes = C(P [[\\]]) / replace_escape,
	escape = C(P [[\]] * S [[nrt"]]) / replace_escape,
	unicode_escape = P "\\u" * (V "hex_digit") ^ 4 ^ -4,
	string_literal = element("literal", Cg(
		                         Ct(
			                         (C((1 - S [["\]])) + V "escape" + V "backslashes" +
				                         V "unicode_escape") ^ 1) / function(chars)
			local buffer = {}
			for _, element in ipairs(chars) do
				table.insert(buffer, string.byte(element))
			end

			return buffer
		end, "val") * Cg(P "" / "bytes", "literaltype")),
	string = element("string",
	                 P "\"" *
		                 Cg(Ct((V "string_literal" + V "splice") ^ 0), "elements") *
		                 P "\"" * V "endpos"),

	tokens = space_tokens(V "comment" + V "paren_list" + V "string" + V "number" +
		                      V "symbol" + V "comma" + V "longstring"),
	token_spacer = S "\t " ^ 0,

	open_paren = P "(" + element("symbol", Cg(P "[" / "braced_list", "str")) +
		element("symbol", Cg(P "{" / "curly-list", "str")),
	close_paren = S ")]}",
	-- LIST SEPARATOR BEHAVIOR IS NOT CONSISTENT BETWEEN BRACED AND NAKED LISTS
	paren_list = list(V "open_paren" *
		                  (list(V "tokens" ^ 1 * P ";") -- ; control character splits list-up-to-point into child list
		+ (P "\\" * V "naked_list") -- \ escape char enters naked list mode from inside a paren list. there's probably an edge case here, indentation is going to be wacky
		+ V "tokens" + V "paren_list" + V "wsp") ^ 1) * V "close_paren", -- tokens and recursion

	empty_line = V "newline" * space_tokens(P "") * #(V "newline" + -1),

	file = list(((V "tokens" * (V "newline" + -1) * V "isdedent") +
		            (V "naked_list_line" ^ -1 * V "newline" * V "isdedent") +
		            (V "naked_list")) ^ 1) * -1,

	naked_list_line = (list(V "tokens" ^ 0 * space_tokens(P ";"))) ^ 1 *
		V "naked_list" ^ 0,
	-- escape char terminates current list 
	naked_list = list( -- escape char terminates current list
	-- TODO: fix this, set up \
	((V "naked_list_line" + V "tokens" ^ 1) ^ 1) *
		(V "empty_line" ^ 1 + (V "newline" * V "indent" *
			(((list(V "tokens" * space_tokens(P ";")) + V "tokens") *
				((#(V "newline" * V "isdedent") * V "dedent") + (-P(1)))) +
				(V "naked_list" * V "dedent")))) ^ 0),

	indent = Cg(Cmt(Cb("indent_level") * V "count_tabs",
	                function(body, position, prev_indent, this_indent)
		if this_indent == nil then this_indent = 0 end

		assert(prev_indent)
		assert(this_indent)

		if this_indent > prev_indent[#prev_indent] then
			table.insert(prev_indent, this_indent)

			return true, prev_indent
		else
			return false
		end
	end), "indent_level"),

	-- SIMPLIFYING ASSUMPTIONS:
	-- I can assume no more than one layer of indent at a time
	dedent = Cg(Cmt(Cb("indent_level"),
	                function(body, position, prev_indent, this_indent)
		table.remove(prev_indent, #prev_indent)
		return true, prev_indent
	end), "indent_level"),

	isdedent = Cmt(Cb("indent_level") * V "count_tabs" ^ 0,
	               function(body, position, prev_indent, this_indent)
		if this_indent == nil then this_indent = 0 end

		assert(prev_indent)
		assert(this_indent)

		return this_indent <= prev_indent[#prev_indent]
	end)

}

local function parse(input, filename)
	assert(filename)
	return lpeg.match(grammar, input, 1, filename)
end

return {parse = parse}
