local gen = require "terms-generators"
local map = gen.declare_map
local array = gen.declare_array

local typed = gen.declare_type()
typed:define_enum("typed", {
	{ "recordcons", { "fields", map(gen.builtin_string, typed) } },
	{ "tuplecons", { "methods", array(typed) } },
})

local map_string_typed = map(gen.builtin_string, typed)
local stuff = map_string_typed()
local funvalue = typed.recordcons(stuff)
p(funvalue)

local stuff2 = map_string_typed()
stuff2:set("foo", funvalue)
local funvalue2 = typed.recordcons(stuff2)
p(funvalue2)

for k, v in pairs(funvalue2.fields) do
	p(k, v)
end

function fail1()
	stuff2:set(2, funvalue)
end
local success_1, err_1 = pcall(fail1)
assert(not success_1)
p(err_1)
function fail2()
	stuff2:set("bar", "baz")
end
local success_2, err_2 = pcall(fail2)
assert(not success_2)
p(err_2)
function fail3()
	stuff2:set("foo", "quux")
end
local success_3, err_3 = pcall(fail3)
assert(not success_3)
p(err_3)

local array_typed = array(typed)
local athing = array_typed()
athing:append(funvalue)
athing[2] = funvalue2
local funvalue3 = typed.tuplecons(athing)
p(funvalue3)
assert(#funvalue3.methods == 2)

for i, v in ipairs(funvalue3.methods) do
	p(i, v)
end

local athing2 = array_typed(funvalue, funvalue2)
p(athing2)
assert(#athing2 == 2)
athing2[1] = funvalue2
p(athing2)
assert(#athing2 == 2)

function fail4()
	athing["lol"] = funvalue
end
local success_4, err_4 = pcall(fail4)
assert(not success_4)
p(err_4)
function fail5()
	athing[2] = "ping"
end
local success_5, err_5 = pcall(fail5)
assert(not success_5)
p(err_5)
function fail6()
	athing[0] = "pong"
end
local success_6, err_6 = pcall(fail6)
assert(not success_6)
p(err_6)
function fail7()
	athing[69] = "nice"
end
local success_7, err_7 = pcall(fail7)
assert(not success_7)
p(err_7)

local name_array = array(gen.builtin_string)
local num_array = array(gen.builtin_number)

local nums = num_array(4, 5, 6, 7, 8)

local snums = nums:map(name_array, function(n)
	return tostring(n)
end)
assert(snums[1] == "4")
assert(snums[4] == "7")
assert(snums[5] == "8")
