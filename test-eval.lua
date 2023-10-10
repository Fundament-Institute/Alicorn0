local terms = require "./terms"
local runtime_context = terms.runtime_context
local typechecking_context = terms.typechecking_context
local inferrable_term = terms.inferrable_term
local typed_term = terms.typed_term
local quantity = terms.quantity
local value = terms.value

local gen = require "./terms-generators"
local map = gen.declare_map
local string_inferrable_map = map(gen.builtin_string, inferrable_term)
local string_typed_map = map(gen.builtin_string, typed_term)
local array = gen.declare_array
local inferrable_array = array(inferrable_term)
local typed_array = array(typed_term)
local value_array = array(value)
local usage_array = array(gen.builtin_number)
local string_array = array(gen.builtin_string)

local function unrestricted(t)
	return value.qtype(value.quantity(quantity.unrestricted), t)
end
local function tup_val(...)
	return value.tuple_value(value_array(...))
end
local function cons(...)
	return value.enum_value("cons", tup_val(...))
end
local empty = value.enum_value("empty", tup_val())

local eval = require "./evaluator"
local const_combinator = eval.const_combinator
local infer = eval.infer
local evaluate = eval.evaluate

print("PART ONE!!!!!!!!!!")

local function eval_test(name, term)
	local initial_context = runtime_context()
	print("TEST: " .. name)
	print("initial")
	print(term:pretty_print())
	local result = evaluate(term, initial_context)
	print("result")
	print(result:pretty_print())
	return result
end

local lit = typed_term.literal
local var = typed_term.bound_variable
local lam = typed_term.lambda
local app = typed_term.application

local num = value.number
local n42 = lit(num(42))
local n69 = lit(num(69))
local n420 = lit(num(420))
local n621 = lit(num(621))
local n926 = lit(num(926))
local n1337 = lit(num(1337))

-- var(1) refers to the outermost bound variable, 2 next outermost, etc
-- as opposed to de bruijn indices, where 1 refers to the innermost (nearest) binding, etc
local id = lam(var(1))
local const = lam(lam(var(1)))
-- in de bruijn indices, these would be lam(var(1)) and lam(lam(var(2))) respectively

local result

local apply_id_with_42 = app(id, n42)
result = eval_test("apply_id_with_42", apply_id_with_42)
assert(result:is_number() and result:unwrap_number() == 42)

local apply_closure_with_capture = app(app(const, n69), n1337)
result = eval_test("apply_closure_with_capture", apply_closure_with_capture)
assert(result:is_number() and result:unwrap_number() == 69)

local apply_partial_closure_with_capture = app(const, n69)
result = eval_test("apply_partial_closure_with_capture", apply_partial_closure_with_capture)

print("PART TWO!!!!!!!!!!")

local function infer_and_eval(name, inf)
	local initial_context = runtime_context()
	local initial_typechecking_context = typechecking_context()
	print("TEST: " .. name)
	print("initial")
	print(inf:pretty_print())
	local result_type, result_usages, result_term = infer(inf, initial_typechecking_context)
	print("result_type")
	print(result_type:pretty_print())
	print("result_usages")
	print(result_usages:pretty_print())
	print("result_term")
	print(result_term:pretty_print())
	local result = evaluate(result_term, initial_context)
	print("result")
	print(result:pretty_print())
	return result
end

local function inf_t(t)
	return inferrable_term.typed(value.star(0), usage_array(), lit(unrestricted(t)))
end
local function inf_typ(t, typ)
	return inferrable_term.typed(unrestricted(t), usage_array(), typ)
end
local inf_var = inferrable_term.bound_variable
local function inf_lam(n, t, b)
	return inferrable_term.annotated_lambda(n, inf_t(t), b)
end
local inf_app = inferrable_term.application

local t_num = value.number_type
local i42 = inf_typ(t_num, n42)
local i69 = inf_typ(t_num, n69)
local i420 = inf_typ(t_num, n420)
local i621 = inf_typ(t_num, n621)
local i926 = inf_typ(t_num, n926)
local i1337 = inf_typ(t_num, n1337)

local inf_id = inf_lam("x", t_num, inf_var(1))
local inf_const = inf_lam("val", t_num, inf_lam("ignored", t_num, inf_var(1)))

local apply_inf_id_with_42 = inf_app(inf_id, i42)
infer_and_eval("apply_inf_id_with_42", apply_inf_id_with_42)

local apply_inf_closure_with_capture = inf_app(inf_app(inf_const, i69), i1337)
infer_and_eval("apply_inf_closure_with_capture", apply_inf_closure_with_capture)

print("PART THREE!!!!!!!!")

local function inf_tup(...)
	return inferrable_term.tuple_cons(inferrable_array(...))
end
local inf_tupelim = inferrable_term.tuple_elim
local tuple_of_69_420 = inf_tup(i69, i420)
infer_and_eval("tuple_of_69_420", tuple_of_69_420)

local inf_swap = inf_tup(inf_var(2), inf_var(1))
local swap_69_420 = inf_tupelim(tuple_of_69_420, inf_swap)
infer_and_eval("swap_69_420", swap_69_420)

print("PART FOUR!!!!!!!!!")

local function prim_f(f)
	return lit(value.prim(f))
end
local prim_add = prim_f(function(left, right)
	return left + right
end)
local function prim_lit(x)
	return lit(value.prim(x))
end
local function prim_tup(...)
	return typed_term.prim_tuple_cons(typed_array(...))
end

local p69 = prim_lit(69)
local p420 = prim_lit(420)
local p621 = prim_lit(621)
local p926 = prim_lit(926)

local prim_add_69_420 = app(prim_add, prim_tup(p69, p420))
eval_test("prim_add_69_420", prim_add_69_420)

local function inf_prim_tup(...)
	return inferrable_term.prim_tuple_cons(inferrable_array(...))
end

local t_prim_num = value.prim_number_type
local ip69 = inf_typ(t_prim_num, p69)
local ip420 = inf_typ(t_prim_num, p420)
local ip621 = inf_typ(t_prim_num, p621)
local ip926 = inf_typ(t_prim_num, p926)

local tuple_of_621_420 = inf_prim_tup(ip621, ip420)
infer_and_eval("tuple_of_621_420", tuple_of_621_420)

local inf_prim_swap = inf_prim_tup(inf_var(2), inf_var(1))
local swap_prim_621_420 = inf_tupelim(tuple_of_621_420, inf_prim_swap)
infer_and_eval("swap_prim_621_420", swap_prim_621_420)

print("PART FIVE!!!!!!!!!")

-- create prim tuple
-- call prim function
-- use tuple elim to extract results and repack with another prim
-- call another primitive function

local primextractrepack = prim_tup(var(1), prim_lit(-1))

local input = prim_tup(prim_lit(2)) -- -> (2)
local returns_input_and_3 = prim_f(function(a)
	return a, 3
end) -- returns_input_and_3(2) -> (2, 3)
local result = app(prim_add, app(returns_input_and_3, input)) -- add(2, 3) -> (5)
local t = typed_term.tuple_elim(result, 1, primextractrepack) -- (5) -> (5, -1)
local result_2 = app(prim_add, t) -- add(5, -1) -> 4
local result_3 = typed_term.tuple_elim(result_2, 1, var(1))
eval_test("repacking_tuples", result_3)

-- local fmt = require './format-adapter'
-- local user_defined_prim_a_id = { name = "syntax" }
-- local user_defined_prim_a_cons = inferrable_term.prim_user_defined_type_cons(user_defined_prim_a_id, inferrable_array())
-- local value_user_defined_prim_a = infer_and_eval("syn_prim_cons", user_defined_prim_a_cons)

-- local prim_fmt_read = prim_f(function(str) return fmt.read(str, "inline") end)
-- local infer_prim_fmt_read = inferrable_term.typed(value_user_defined_prim_a, usage_array(), typed_term.literal(value.prim(prim_fmt_read)))
-- infer_and_eval("user_defined_prim_syntax_cons", inf_app(infer_prim_fmt_read, inferrable_term.typed(value.prim_string_type, usage_array(), prim_lit("+ 2 3"))))

print("PART SIX!!!!!!!!!!")

local cupnum = const_combinator(unrestricted(t_prim_num))
local tuple_decl = unrestricted(value.prim_tuple_type(cons(cons(empty, cupnum), cupnum)))
local mogrify = prim_f(function(left, right)
	return left + right, left - right
end)
local inf_mogrify = inf_typ(value.prim_function_type(tuple_decl, tuple_decl), mogrify)
local apply_mogrify_with_621_420 = inf_app(inf_mogrify, tuple_of_621_420)
infer_and_eval("apply_mogrify_with_621_420", apply_mogrify_with_621_420)

print("PART SEVEN!!!!!!!!")
local function desc2map(t, map_desc)
	local map = t()
	local odd = true
	local key
	for _, v in ipairs(map_desc) do
		if odd then
			key = v
		else
			map[key] = v
		end
		odd = not odd
	end
	return map
end
local function inf_rec(map_desc)
	local map = desc2map(string_inferrable_map, map_desc)
	return inferrable_term.record_cons(map)
end
local inf_recelim = inferrable_term.record_elim

local record_621_926 = inf_rec({ "foo", i621, "bar", i926 })
infer_and_eval("record_621_926", record_621_926)

local record_swap = inf_rec({ "baz", inf_var(2), "quux", inf_var(1) })
local swap_621_926 = inf_recelim(record_621_926, string_array("foo", "bar"), record_swap)
infer_and_eval("swap_621_926", swap_621_926)

local record_prim_621_926 = inf_rec({ "foo", ip621, "bar", ip926 })
local tuple_conv = inf_prim_tup(inf_var(1), inf_var(2))
local record_conv = inf_rec({ "sum", inf_var(1), "difference", inf_var(2) })
local megamogrify = inf_tupelim(
	inf_app(inf_mogrify, inf_recelim(record_prim_621_926, string_array("foo", "bar"), tuple_conv)),
	record_conv
)
infer_and_eval("megamogrify", megamogrify)

print("PART EIGHT!!!!!!!!")

local enum_foo_prim_69 = typed_term.enum_cons("foo", p69)
local prim_add_1 = prim_f(function(x)
	return x + 1
end)
local prim_subtract_1 = prim_f(function(x)
	return x - 1
end)
local primtupify = lam(app(var(2), prim_tup(var(1))))
local untupify = var(1)
local add_1 = app(primtupify, prim_add_1)
local subtract_1 = app(primtupify, prim_subtract_1)
local obj_foo_bar = typed_term.object_cons(desc2map(string_typed_map, { "foo", add_1, "bar", subtract_1 }))
local typed_enum_elim = typed_term.tuple_elim(typed_term.enum_elim(enum_foo_prim_69, obj_foo_bar), 1, untupify)
eval_test("typed_enum_elim", typed_enum_elim)

local typed_object_elim = typed_term.tuple_elim(typed_term.object_elim(obj_foo_bar, enum_foo_prim_69), 1, untupify)
eval_test("typed_object_elim", typed_object_elim)
