local PrettyPrint = require "./pretty-printer".PrettyPrint
local luaunit = require "luaunit"
local terms_gen = require "./terms-generators"
local terms = require "./terms"

local value_array = terms_gen.declare_array(terms.value)
-- if this require fails you need to `lit install luvit/tap`
local passed, failed, total = (require "tap")(function(test)
	-- test cases are assuming that fitsinto(not a type, _) or fitinto(_, not a type)
	-- returns false, errormessage
	-- but it would probably be fine for passing things that aren't types into fitsinto
	-- to throw a lua error() instead
	-- important part is that it doesn't return true!

	test("empty pretty printer result is empty", function(expect)
		local pp = PrettyPrint.new()
		assert(tostring(pp) == "")
	end)

	test("array", function(expect)
		local pp = PrettyPrint.new()
		pp:any(value_array({ terms.value.prim_number_type, terms.value.prim_number_type }))
		luaunit.assertEquals(tostring(pp), "[value.prim_number_type, value.prim_number_type]")
	end)

	test("simple unit type", function(expect)
		local pp = PrettyPrint.new()
		pp:unit("values.level_type")
		assert(tostring(pp) == "values.level_type")
	end)

	test("simple record type", function(expect)
		local pp = PrettyPrint.new()
		pp:record("values.any", { { "value", "something" } })
		luaunit.assertEquals(tostring(pp), [[values.any("something")]])
	end)

	test("complex record type", function(expect)
		local pp = PrettyPrint.new()
		pp:record("values.table", {
			{ "int", 1 },
			{ "value", "something" },
		})
		luaunit.assertEquals(
			tostring(pp),
			[[values.table {
 int = 1,
 value = "something",
}]]
		)
	end)
end)
