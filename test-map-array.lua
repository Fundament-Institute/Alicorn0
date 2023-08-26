local gen = require './terms-generators'
local map = gen.declare_map

local typed = gen.declare_type()
typed:define_enum("typed", {
  {"recordcons", {"fields", map(gen.builtin_string, typed)}},
  {"objectcons", {"methods", map(gen.builtin_string, typed)}},
})

local map_string_typed = map(gen.builtin_string, typed)
local stuff = map_string_typed()
local funvalue = typed.recordcons(stuff)
p(funvalue)

local stuff2 = map_string_typed()
stuff2["foo"] = funvalue
local funvalue2 = typed.recordcons(stuff2)
p(funvalue2)

function fail1()
  stuff2[2] = funvalue
end
local success_1, err_1 = pcall(fail1)
assert(not success_1)
p(err_1)
function fail2()
  stuff2["bar"] = "baz"
end
local success_2, err_2 = pcall(fail2)
assert(not success_2)
p(err_2)
function fail3()
  stuff2["foo"] = "quux"
end
local success_3, err_3 = pcall(fail3)
assert(not success_3)
p(err_3)
