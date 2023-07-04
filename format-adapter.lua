local metalanguage = require 'metalanguage'
local format = require 'format'
local types = require './typesystem'


local function syntax_convert(tree)
  if tree.kind == "list" then
    local res = metalanguage.nilval
    for i = #tree.elements, 1, -1 do
      res = metalanguage.pair(tree.anchor, syntax_convert(tree.elements[i]), res)
    end
    return res
  elseif tree.kind == "symbol" then
    return metalanguage.symbol(tree.anchor, tree.str)
  elseif tree.kind == "literal" then
    if tree.literaltype == "f64" then
      -- metalanguage.value use here is only correct for smoketest language and will need changed in future
      return metalanguage.value(tree.anchor, {type = types.number, val = tree.val})
    else
      error "syntax contains a literal of a type other than the basic number"
    end
  elseif tree.kind == "string" then
    error "syntax contains a string which isn't yet implemented"
  else
    error "syntax contains an unknown kind"
  end
end

local function read(text, source)
  local buffer = format.parse(text, source)
  return syntax_convert(buffer)
end

return {
  read = read
}
