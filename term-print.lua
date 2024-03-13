local gen = require "./terms-generators"
local derivers = require "./derivers"

local blarg = gen.declare_type()
local bling = gen.declare_type()
local blong = gen.declare_type()
local bloop = gen.declare_type()

blarg:define_enum("blarg", {
	{ "foo" },
	{ "bar", { "bingle", blarg, "binky", blarg } },
	{ "baz", { "num", gen.builtin_number, "str", gen.builtin_string } },
	{ "quux", { "ziggle", blarg } },
	{ "flux", { "pb", blarg, "em", blarg } },
	{ "add", { "left", blarg, "right", blarg } },
	{ "mult", { "left", blarg, "right", blarg } },
	{ "bling", { "bling", bling } },
	{ "blong", { "blong", blong } },
})

bling:define_record("bling", { "num", gen.builtin_number, "str", gen.builtin_string })
blong:define_record("blong", { "str", gen.builtin_string })

local bloop_array = gen.declare_array(bloop)

bloop:define_enum("bloop", {
	{ "cons", { "array", gen.declare_array(bloop) } },
	{ "pros", { "blong", blong } },
})

blarg:derive(derivers.as)

local blarg_override_pretty = {
	bar = function(self, pp, extra)
		local bingle, binky = self:unwrap_bar()
		extra = extra or ""

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("bar\n")
		pp:unit(pp:_resetcolor())

		pp:_indent()
		pp:_prefix()
		pp:any(bingle, extra)
		pp:unit(extra)
		pp:unit("\n")
		pp:_dedent()

		--[[
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
			pp:any(bingle, extra)
			pp:unit(extra)
			pp:unit("\n")
			pp:_dedent()

			binky = unwrap_if_quux(binky)
		end
		--]]

		pp:_prefix()
		pp:unit(pp:_color())
		pp:unit("in\n")
		pp:unit(pp:_resetcolor())

		pp:_indent()
		pp:_prefix()
		pp:any(binky, extra)
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
	--quux = function(self, pp, ...)
	--	pp:any(self.ziggle, ...)
	--end,
	add = function(self, pp, ...)
		local left, right = self:unwrap_add()

		if left:is_add() or left:is_mult() then
			pp:any(left, ...)
		else
			pp:unit("(")
			pp:any(left, ...)
			pp:unit(")")
		end

		pp:unit("+")

		if right:is_add() or right:is_mult() then
			pp:any(right, ...)
		else
			pp:unit("(")
			pp:any(right, ...)
			pp:unit(")")
		end
	end,
	mult = function(self, pp, ...)
		local left, right = self:unwrap_mult()

		if left:is_mult() then
			pp:any(left, ...)
		else
			pp:unit("(")
			pp:any(left, ...)
			pp:unit(")")
		end

		pp:unit("*")

		if right:is_mult() then
			pp:any(right, ...)
		else
			pp:unit("(")
			pp:any(right, ...)
			pp:unit(")")
		end
	end,
}

bloop:derive(derivers.as)

local bloop_override_pretty = {
	--cons = function(self, pp, extra)
	--	local array = self:unwrap_cons()
	--end,
	pros = function(self, pp, extra)
		local blong = self:unwrap_pros()
		pp:unit(extra)
		pp:any(blong, extra)
	end,
}

blarg:derive(derivers.pretty_print, blarg_override_pretty)
bling:derive(derivers.pretty_print)
blong:derive(derivers.pretty_print)
bloop:derive(derivers.pretty_print, bloop_override_pretty)

print(blarg.foo)

local b = blarg.baz(420, "blazeit")
for i = 1, 5 do
	b = blarg.bar(blarg.foo, b)
	b = blarg.quux(b)
	print(b:pretty_print(" woah!!!"))
end
print(blarg.flux(blarg.foo, b):pretty_print(" woah2"))

local c = blarg.add(blarg.foo, blarg.foo)
for i = 1, 5 do
	c = blarg.add(c, blarg.foo)
end
c = blarg.mult(blarg.foo, c)
print(c)

print(blarg.bling(bling(69, "nice")))
print(blarg.blong(blong("foobar")))

print(bloop.pros(blong("wheeze")):pretty_print("what? "))
print(bloop.cons(bloop_array(bloop.pros(blong("wheeze")))):pretty_print("what? "))
