local metalanguage = require 'metalanguage'
local format = require 'temp-format'

local function syntax_convert(tree)
  if tree.kind == "list" then
    local res = metalanguage.nilval
    for i = #tree.elements, 1, -1 do
      res = metalanguage.pair(syntax_convert(tree.elements[i]), res)
    end
    return res
  elseif tree.kind == "symbol" then
    return metalanguage.symbol(tree.str)
  elseif tree.kind == "literal" then
    if tree.literaltype == "f64" then
      return metalanguage.value(tree.val)
      -- error "syntax contains a number literal which should be accepted but is NYI"
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
