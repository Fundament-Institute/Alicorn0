local gen = require './terms-generators'

local mytype1 = gen.declare_enum("mytype1", {
  {"foo"},
  {"bar"},
  {"baz"},
})

local mytype2 = gen.declare_enum("mytype2", {
  {"truer"},
  {"middle", {"thing", mytype1}},
  {"falser"},
})

local mytype3 = gen.declare_record("mytype3", {
  "one", mytype1,
  "anotherone", mytype2,
})

local mytype3butsimple = gen.declare_record("mytype3", {
  "one", gen.builtin_number,
  "anotherone", gen.builtin_number,
})

local eq = {
  record = function(t, info)
    local checks = {}
    for i, param in ipairs(info.params) do
      checks[i] = string.format("left[%q] == right[%q]", param, param)
    end
    local all_checks = table.concat(checks, " and ")
    local chunk = "return function(left, right) return " .. all_checks .. " end"
    print("record chunk:")
    print("###")
    print(chunk)
    print("###")
    local compiled, message = load(chunk)
    assert(compiled, message)
    local eq_fn = compiled()
    t.__eq = eq_fn
  end,
  enum = function(t, info)
    local variants_checks = {}
    for n, vname in ipairs(info.variants) do
      local vkind = info.name .. "_" .. vname
      local vinfo = info.variants[vname].info
      local checks = {}
      for i, param in ipairs(vinfo.params) do
        checks[i] = string.format("left[%q] == right[%q]", param, param)
      end
      local all_checks = table.concat(checks, " and ")
      local entry = string.format("[%q] = function(left, right) return %s end", vkind, all_checks)
      variants_checks[n] = entry
    end
    local all_variants_checks = "{\n  " .. table.concat(variants_checks, ",\n  ") .. "\n}"
    local define_all_variants_checks = "local all_variants_checks = " .. all_variants_checks

    local kind_check_expression = "left.kind == right.kind"
    local variant_check_expression = "all_variants_checks[left.kind](left, right)"
    local check_expression = kind_check_expression .. " and " .. variant_check_expression
    local check_function = "function(left, right) return " .. check_expression .. " end"

    local chunk = define_all_variants_checks .. "\nreturn " .. check_function
    print("enum chunk:")
    print("###")
    print(chunk)
    print("###")
    local compiled, message = load(chunk)
    assert(compiled, message)
    local eq_fn = compiled()
    t.__eq = eq_fn
  end,
}

p("simple")
mytype3butsimple:derive(eq)
local x = mytype3butsimple(69, 420)
local y = mytype3butsimple(420, 69)
local z = mytype3butsimple(69, 420)
p(x == y)
p(x == z)
p(y == z)

p("2")
-- beware of bugs if mytype2 doesn't derive eq
-- mytype1 is an enum with only unit cases, so equality is trivial
mytype2:derive(eq)
mytype3:derive(eq)
local x2 = mytype3(mytype1.foo, mytype2.truer)
local y2 = mytype3(mytype1.bar, mytype2.truer)
local y3 = mytype3(mytype1.bar, mytype2.truer)
local z2 = mytype3(mytype1.foo, mytype2.falser)
local a2 = mytype3(mytype1.foo, mytype2.middle(mytype1.bar))
local b2 = mytype3(mytype1.foo, mytype2.middle(mytype1.baz))
local c2 = mytype3(mytype1.foo, mytype2.middle(mytype1.baz))
p(x2 == y2)
p(x2 == z2)
p(x2 == a2)
p(x2 == b2)
p(y2 == z2)
p(y2 == a2)
p(y2 == b2)
p(z2 == a2)
p(z2 == b2)
p(a2 == b2)
p(b2 == c2)
p(y2 == y3)
