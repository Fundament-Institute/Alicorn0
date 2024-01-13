local traits = require "./traits"

local prettyprintable = traits.declare_trait("prettyprintable")
prettyprintable:declare_method("print")

return prettyprintable
