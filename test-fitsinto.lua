local traits = require "./traits"
local terms = require "./terms"
local gen = require "./terms-generators"
local evaluator = require "./evaluator"

local value = terms.value
local typed = terms.typed_term
local fitsinto = evaluator.fitsinto

local val_array = gen.declare_array(value)

local function val_tup_cons(...)
	return value.tuple_value(val_array(...))
end
local function val_desc_elem(x)
	return value.enum_value("cons", x)
end
local val_desc_empty = value.enum_value("empty", val_tup_cons())

local function expect_error(fn, err_txt, ...)
	local ok, err = pcall(fn, ...)
	assert(not ok)
	if err_txt then
		assert(
			err_txt == err or tostring(err):find(err_txt),
			"err didn't contain " .. err_txt .. " was instead " .. err
		)
	end
end

-- if this require fails you need to `lit install luvit/tap`
local passed, failed, total = (require "tap")(function(test)
	-- test cases are assuming that fitsinto(not a type, _) or fitinto(_, not a type)
	-- returns false, errormessage
	-- but it would probably be fine for passing things that aren't types into fitsinto
	-- to throw a lua error() instead
	-- important part is that it doesn't return true!

	test("should fail for non-type which don't match content", function(expect)
		-- should fail because number isn't a type
		expect_error(function()
			fitsinto(value.number(1), value.number(2))
		end, "isn't a type")
	end)
	test("should fail for non-type which do match content", function(expect)
		local one = value.number(1)
		-- should fail because number isn't a type
		expect_error(function()
			fitsinto(one, one)
		end, "isn't a type")
		-- try again but different instances
		expect_error(function()
			fitsinto(value.number(1), value.number(1))
		end, "isn't a type")
	end)
	test("should fail for unrelated non-type values", function(expect)
		expect_error(function()
			fitsinto(value.number(1), value.operative_value(value.number(1)))
		end, "isn't a type")
	end)

	test("prim_number_type into prim_number_type should fitsinto", function(expect)
		assert(fitsinto(value.prim_number_type, value.prim_number_type))
	end)

	test("prim_number_type into prim_string_type should not fitsinto", function(expect)
		assert(not fitsinto(value.prim_number_type, value.prim_string_type))
	end)

	test("prim_string_type into prim_number_type should not fitsinto", function(expect)
		assert(not fitsinto(value.prim_string_type, value.prim_number_type))
	end)

	-- test type of type into star(0), should work
	test("type into star", function(expect)
		local initial = value.prim_type_type
		local successor = value.star(0)
		assert(fitsinto(initial, successor))
	end)

	-- test prim_number_type into star(0), should not work
	test("type into star", function(expect)
		local initial = value.prim_number_type
		local successor = value.star(0)
		assert(not fitsinto(initial, successor))
	end)

	test("prim_type_type into star(0..5)", function(expect)
		for i = 0, 5 do
			local initial = value.prim_type_type
			local successor = value.star(i)
			assert(fitsinto(initial, successor))
		end
	end)

	-- test type into star(n) into star(n + 1), should work
	test("star successors", function(expect)
		for i = 1, 5 do
			local initial = value.star(i)
			local successor = value.star(i + 1)
			assert(fitsinto(initial, successor))
		end
	end)

	-- test type into star(n) into star(n * 3), should work
	test("star successors with gap", function(expect)
		for i = 0, 5 do
			local initial = value.star(i)
			local successor = value.star(i * 3)
			assert(fitsinto(initial, successor))
		end
	end)

	-- test type into star(n + 2) into star(n), should not work
	test("star prevs", function(expect)
		for i = 0, 5 do
			local initial = value.star(i + 2)
			local successor = value.star(i)
			assert(not fitsinto(initial, successor))
		end
	end)

	-- testing two tuple type decls that are the same, should work
	test("tuple type decl", function(expect)
		-- fitsinto needs to handle tuple type by applying the closures on prior element (from right side always)
		-- not by blindly applying closure like it is right now
		local names = gen.declare_array(gen.builtin_string)
		local decl_a = value.tuple_type(
			val_desc_elem(
				val_tup_cons(
					val_desc_elem(
						val_tup_cons(
							val_desc_empty,
							value.closure(
								"A",
								typed.tuple_elim(names(), typed.bound_variable(1), 0, typed.star(1)),
								terms.runtime_context()
							)
						)
					),
					value.closure(
						"B",
						terms.typed_term.tuple_elim(
							names("FOO"),
							terms.typed_term.bound_variable(1),
							1,
							typed.bound_variable(2)
						),
						terms.runtime_context()
					)
				)
			)
		)
		local decl_b = value.tuple_type(
			val_desc_elem(
				val_tup_cons(
					val_desc_elem(
						val_tup_cons(
							val_desc_empty,
							value.closure(
								"C",
								typed.tuple_elim(names(), typed.bound_variable(1), 0, typed.star(1)),
								terms.runtime_context()
							)
						)
					),
					value.closure(
						"D",
						terms.typed_term.tuple_elim(
							names("BAR"),
							terms.typed_term.bound_variable(1),
							1,
							typed.bound_variable(2)
						),
						terms.runtime_context()
					)
				)
			)
		)
		assert(fitsinto(decl_a, decl_b))
	end)
end)
