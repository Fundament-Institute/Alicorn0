local traits = require "traits"

local pretty_printable = traits.declare_trait("pretty_printable")
pretty_printable:declare_method("print")

return pretty_printable
