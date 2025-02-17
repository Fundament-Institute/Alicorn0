-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local metalanguage = require "metalanguage"
local format = require "format"

local function syntax_convert(tree)
	if tree.kind == "list" then
		local res = metalanguage.new_nilval(tree.span)
		for i = #tree.elements, 1, -1 do
			local elem = syntax_convert(tree.elements[i])
			if elem then -- special handling for comments...
				res = metalanguage.pair(tree.span, elem, res)
			end
		end
		return res
	elseif tree.kind == "symbol" then
		assert(tree["kind"])
		return metalanguage.symbol(tree.span, tree)
	elseif tree.kind == "literal" then
		local tree_span = tree.span
		return metalanguage.value(tree_span, { type = tree.literaltype, val = tree.val, span = tree_span })
	elseif tree.kind == "string" then
		if type(tree.elements) == "string" then
			local tree_span = tree.span
			return metalanguage.value(tree_span, { type = "string", val = tree.elements, span = tree_span })
		end
		if #tree.elements ~= 1 or tree.elements[1].literaltype ~= "bytes" then
			error "NYI: strings with splices / not exactly one literal"
		end

		-- converting this to a string here is a temporary simplification, remove when NYI above is fixed.
		---@type [string]
		local chars = {}
		for i, byte in ipairs(tree.elements[1].val) do
			chars[i] = string.char(byte)
		end
		local val = table.concat(chars)
		local tree_span = tree.span
		return metalanguage.value(tree_span, { type = "string", val = val, span = tree_span })
	elseif tree.kind == "comment" then
		--do nothing
	else
		error(("syntax contains an unknown kind %q"):format(tree.kind))
	end
end

local function read(text, source)
	local buffer = format.parse(text, source)
	return syntax_convert(buffer)
end

local lispy_indent = "\t"
local lispy_break = 100
---@param code ConstructedSyntax
---@param d integer?
---@return string
local function lispy_print(code, d)
	if d == nil then
		d = 0
	end
	local start_anchor_pfx = ""
	if code.span ~= nil then
		start_anchor_pfx = "#|" .. tostring(code.span.start) .. "…|# "
	end
	local stop_anchor_sfx = ""
	if code.span.start ~= code.span.stop then
		stop_anchor_sfx = " #|…" .. tostring(code.span.stop) .. "|#"
	end
	if code.accepters.Pair then
		local hd = code[1]
		local tl = code[2]
		local continue = true
		local n = 0
		local a = {}
		local t = 0
		while continue do
			n = n + 1
			a[n] = lispy_print(hd, d + 1)
			t = t + #a[n]
			t = t + 1
			if tl.accepters.Pair then
				hd = tl[1]
				tl = tl[2]
			else
				continue = false
			end
		end
		local pfx = ""
		for i = 1, d do
			pfx = pfx .. lispy_indent
		end
		local pfx1 = pfx .. lispy_indent
		if t >= lispy_break then
			return ("%s(\n%s%s\n%s)%s"):format(
				start_anchor_pfx,
				pfx1,
				table.concat(a, "\n" .. pfx1),
				pfx,
				stop_anchor_sfx
			)
		else
			return ("%s(%s)%s"):format(start_anchor_pfx, table.concat(a, " "), stop_anchor_sfx)
		end
	elseif code.accepters.Symbol then
		local name = code[1]
		return start_anchor_pfx .. name.str .. stop_anchor_sfx
	elseif code.accepters.Value then
		local val = code[1]
		local sval = string.gsub(tostring(val.val), "%c", "")
		if #sval > 10 then
			sval = string.sub(sval, 1, 10) .. "..."
		end
		return ("%sval[%s](%s)%s"):format(start_anchor_pfx, val.type, sval, stop_anchor_sfx)
	elseif code.accepters.Nil then
		return start_anchor_pfx .. "()" .. stop_anchor_sfx
	else
		error(start_anchor_pfx .. "awa" .. stop_anchor_sfx)
	end
end

local format_adapter = {
	read = read,
	lispy_print = lispy_print,
}
local internals_interface = require "internals-interface"
internals_interface.format_adapter = format_adapter
return format_adapter
