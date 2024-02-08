local gen = require "./terms-generators"
local derivers = require "./derivers"

local blarg = gen.declare_type()

blarg:define_enum("blarg", {
	{ "foo" },
	{ "bar", { "bingle", blarg, "binky", blarg } },
	{ "baz", { "num", gen.builtin_number, "str", gen.builtin_string } },
	{ "quux", { "ziggle", blarg } },
	{ "flux", { "pb", blarg, "em", blarg } },
})

blarg:override_pretty({
	bar = function(self, pp)
		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("bar\n")
		pp:unit(pp:_resetcolor())

		pp:_indent()
		pp:_prefix()
		pp:any(self.bingle)
		pp:unit("\n")
		pp:_dedent()

		pp:_prefix()
		pp:unit(pp:_color())
		pp:unit("in\n")
		pp:unit(pp:_resetcolor())

		pp:_indent()
		pp:_prefix()
		pp:any(self.binky)
		pp:unit("\n")
		pp:_dedent()

		pp:_prefix()
		pp:unit(pp:_color())
		pp:unit(";")
		pp:unit(pp:_resetcolor())

		pp:_exit()
	end,
	baz = function(self, pp)
		pp:unit("{n:")
		pp:any(self.num)
		pp:unit(",s:")
		pp:any(self.str)
		pp:unit("}")
	end,
})

blarg:derive(derivers.pretty_print)

print(blarg.foo)

local b = blarg.baz(420, "blazeit")
for i = 1, 5 do
	b = blarg.bar(b, blarg.foo)
	b = blarg.quux(b)
	print(b)
end
print(blarg.flux(blarg.foo, b))
