local gen = require "./terms-generators"
local derivers = require "./derivers"

local blarg = gen.declare_type()

blarg:define_enum("blarg", {
	{ "foo" },
	{ "bar", { "bingle", blarg, "binky", blarg } },
	{ "baz", { "num", gen.builtin_number, "str", gen.builtin_string } },
	{ "quux", { "ziggle", blarg } },
	{ "flux", { "pb", blarg, "em", blarg } },
	{ "add", { "left", blarg, "right", blarg } },
	{ "mult", { "left", blarg, "right", blarg } },
})

blarg:derive(derivers.as)

blarg.override_pretty = {
	bar = function(self, pp)
		local bingle, binky = self:unwrap_bar()

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("bar\n")
		pp:unit(pp:_resetcolor())

		pp:_indent()
		pp:_prefix()
		pp:any(bingle)
		pp:unit("\n")
		pp:_dedent()

		local function unwrap_if_quux(q)
			local ok, ziggle = q:as_quux()
			if ok then
				return ziggle
			else
				return q
			end
		end

		binky = unwrap_if_quux(binky)

		while binky:is_bar() do
			bingle, binky = binky:unwrap_bar()

			pp:_indent()
			pp:_prefix()
			pp:any(bingle)
			pp:unit("\n")
			pp:_dedent()

			binky = unwrap_if_quux(binky)
		end

		pp:_prefix()
		pp:unit(pp:_color())
		pp:unit("in\n")
		pp:unit(pp:_resetcolor())

		pp:_indent()
		pp:_prefix()
		pp:any(binky)
		--pp:unit("\n")
		pp:_dedent()

		--pp:_prefix()
		--pp:unit(pp:_color())
		--pp:unit(";")
		--pp:unit(pp:_resetcolor())

		pp:_exit()
	end,
	baz = function(self, pp)
		pp:unit("{n:")
		pp:any(self.num)
		pp:unit(",s:")
		pp:any(self.str)
		pp:unit("}")
	end,
	quux = function(self, pp)
		pp:any(self.ziggle)
	end,
	add = function(self, pp)
		local left, right = self:unwrap_add()

		if left:is_add() or left:is_mult() then
			pp:any(left)
		else
			pp:unit("(")
			pp:any(left)
			pp:unit(")")
		end

		pp:unit("+")

		if right:is_add() or right:is_mult() then
			pp:any(right)
		else
			pp:unit("(")
			pp:any(right)
			pp:unit(")")
		end
	end,
	mult = function(self, pp)
		local left, right = self:unwrap_mult()

		if left:is_mult() then
			pp:any(left)
		else
			pp:unit("(")
			pp:any(left)
			pp:unit(")")
		end

		pp:unit("*")

		if right:is_mult() then
			pp:any(right)
		else
			pp:unit("(")
			pp:any(right)
			pp:unit(")")
		end
	end,
}

blarg:derive(derivers.pretty_print)

print(blarg.foo)

local b = blarg.baz(420, "blazeit")
for i = 1, 5 do
	b = blarg.bar(blarg.foo, b)
	b = blarg.quux(b)
	print(b)
end
print(blarg.flux(blarg.foo, b))

local c = blarg.add(blarg.foo, blarg.foo)
for i = 1, 5 do
	c = blarg.add(c, blarg.foo)
end
c = blarg.mult(blarg.foo, c)
print(c)
