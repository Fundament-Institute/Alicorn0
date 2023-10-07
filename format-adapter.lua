local metalanguage = require './metalanguage'
local format = require './format'

local function syntax_convert(tree)
  if tree.kind == "list" then
    local res = metalanguage.nilval
    for i = #tree.elements, 1, -1 do
			local elem = syntax_convert(tree.elements[i])
			if elem then -- special handling for comments...
				res = metalanguage.pair(tree.anchor, elem, res)
			end
    end
    return res
  elseif tree.kind == "symbol" then
    return metalanguage.symbol(tree.anchor, tree.str)
  elseif tree.kind == "literal" then
    return metalanguage.value(tree.anchor, {type = tree.literaltype, val = tree.val})
  elseif tree.kind == "string" then
		if #tree.elements ~= 1 or tree.elements[1].literaltype ~= "bytes" then
			error "NYI: strings with splices / not exactly one literal"
		end

		-- converting this to a string here is a temporary simplification, remove when NYI above is fixed.
		local chars = {}
		for i, byte in ipairs(tree.elements[1].val) do
			chars[i] = string.char(byte)
		end
		local val = table.concat(chars)
		return metalanguage.value(tree.anchor, {type = "string", val = val})
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

return {
  read = read
}
