local metalanguage = require 'metalanguage'
local format = require 'temp-format'
local types = require './typesystem'

local anchor_mt = {
  __tostring = function(self)
    return "in file" .. self.sourceid .. ", line " .. self.line .. " character " .. self.char
  end
}

local function anchor(anchor) 
  if anchor then
    return setmetatable(anchor, anchor_mt)
  else
    return anchor
  end
end

local function syntax_convert(tree)
  if tree.kind == "list" then
    local res = metalanguage.nilval
    for i = #tree.elements, 1, -1 do
      res = metalanguage.pair(anchor(tree.anchor), syntax_convert(tree.elements[i]), res)
    end
    return res
  elseif tree.kind == "symbol" then
    return metalanguage.symbol(anchor(tree.anchor), tree.str)
  elseif tree.kind == "literal" then
    if tree.literaltype == "f64" then
      -- metalanguage.value use here is only correct for smoketest language and will need changed in future
      return metalanguage.value(anchor(tree.anchor), {type = types.number, val = tree.val})
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
