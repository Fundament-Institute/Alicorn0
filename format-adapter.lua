local metalanguage = require "metalanguage"
local format = require "format"

local function syntax_convert(tree)
	if tree.kind == "list" then
		local res = metalanguage.nilval
		for i = #tree.elements, 1, -1 do
			local elem = syntax_convert(tree.elements[i])
			if elem then -- special handling for comments...
				res = metalanguage.pair(tree.start_anchor, elem, res)
			end
		end
		return res
	elseif tree.kind == "symbol" then
		return metalanguage.symbol(tree.start_anchor, tree.str)
	elseif tree.kind == "literal" then
		return metalanguage.value(tree.start_anchor, { type = tree.literaltype, val = tree.val })
	elseif tree.kind == "string" then
		if type(tree.elements) == "string" then
			return metalanguage.value(tree.start_anchor, { type = "string", val = tree.elements })
		end
		if #tree.elements ~= 1 or tree.elements[1].literaltype ~= "bytes" then
			error "NYI: strings with splices / not exactly one literal"
		end

		-- converting this to a string here is a temporary simplification, remove when NYI above is fixed.
		local chars = {}
		for i, byte in ipairs(tree.elements[1].val) do
			chars[i] = string.char(byte)
		end
		local val = table.concat(chars)
		return metalanguage.value(tree.start_anchor, { type = "string", val = val })
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
local function lispy_print(code, d)
	if d == nil then
		d = 0
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
			return ("(\n%s%s\n%s)"):format(pfx1, table.concat(a, "\n" .. pfx1), pfx)
		else
			return ("(%s)"):format(table.concat(a, " "))
		end
	elseif code.accepters.Symbol then
		local name = code[1]
		return name
	elseif code.accepters.Value then
		local val = code[1]
		local sval = string.gsub(tostring(val.val), "%c", "")
		if #sval > 10 then
			sval = string.sub(sval, 1, 10) .. "..."
		end
		return ("val[%s](%s)"):format(val.type, sval)
	elseif code.accepters.Nil then
		return "()"
	else
		error("awa")
	end
end

local format_adapter = {
	read = read,
	lispy_print = lispy_print,
}
local internals_interface = require "internals-interface"
internals_interface.format_adapter = format_adapter
return format_adapter
