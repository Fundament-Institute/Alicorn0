local derivers = require "./derivers"
local pretty_print = derivers.pretty_print
local gen = require "./terms-generators"

local mytype1 = gen.declare_enum("mytype1", {
	{ "foo" },
	{ "bar" },
	{ "baz" },
})

local mytype2 = gen.declare_enum("mytype2", {
	{ "truer" },
	{ "middle", { "thing", mytype1 } },
	{ "falser" },
})

local mytype3 = gen.declare_record("mytype3", {
	"one",
	mytype1,
	"anotherone",
	mytype2,
})

local nest1 = gen.declare_type()
nest1:define_enum("nest", {
	{ "n", { "a", nest1 } },
	{ "base", { "mt3", mytype3 } },
})

local mytype3butsimple = gen.declare_record("mytype3simple", {
	"one",
	gen.builtin_number,
	"anotherone",
	gen.builtin_number,
})

for _, t in ipairs { mytype1, mytype2, mytype3, nest1, mytype3butsimple } do
	t:derive(pretty_print)
end
local x = mytype3butsimple(69, 420)

local x2 = mytype3(mytype1.foo, mytype2.truer)
local y2 = mytype3(mytype1.bar, mytype2.truer)
local y3 = mytype3(mytype1.bar, mytype2.truer)
local z2 = mytype3(mytype1.foo, mytype2.falser)
local a2 = mytype3(mytype1.foo, mytype2.middle(mytype1.bar))
local b2 = mytype3(mytype1.foo, mytype2.middle(mytype1.baz))
local c2 = mytype3(mytype1.foo, mytype2.middle(mytype1.baz))
local n = nest1.n(nest1.n(nest1.n(nest1.n(nest1.n(nest1.n(nest1.base(x2)))))))
print(x:pretty_print())
print(x2:pretty_print())
print(n:pretty_print())
print(n)

assert(tostring(n) == n:pretty_print())

local PrettyPrint = require "./pretty-printer".PrettyPrint
local pp = PrettyPrint:new()
pp:any(n)
print(pp)
