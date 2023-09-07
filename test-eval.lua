local gen = require './terms-generators'
local terms = require './terms'
local eval = require './evaluator'

print("PART ONE!!!!!!!!!!")

local function eval_test(name, term)
  local initial_context = terms.runtime_context()
  print("test: " .. name)
  p("initial", term)
  local result = eval.evaluate(term, initial_context)
  p("result", result)
  return result
end

local lit = terms.typed_term.literal
local var = terms.typed_term.bound_variable
local lam = terms.typed_term.lambda
local app = terms.typed_term.application

local num = terms.value.number
local n42 = lit(num(42))
local n69 = lit(num(69))
local n420 = lit(num(420))
local n621 = lit(num(621))
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

print("PART TWO!!!!!!!!!!")

local function infer_and_eval(name, inf)
  local initial_context = terms.runtime_context()
  local initial_typechecking_context = terms.typechecking_context()
  print("test: " .. name)
  p("initial", inf)
  local result_type, result_usages, result_term = eval.infer(inf, initial_typechecking_context)
  p("result_type", result_type)
  p("result_usages", result_usages)
  p("result_term", result_term)
  local result = eval.evaluate(result_term, initial_context)
  p("result", result)
  return result
end

local array = gen.declare_array
local usage_array = array(gen.builtin_number)
local inferrable_array = array(terms.inferrable_term)
local typed_array = array(terms.typed_term)

local function unrestricted(t) return terms.value.qtype(terms.value.quantity(terms.quantity.unrestricted), t) end
local function inf_t(t) return terms.inferrable_term.typed(terms.value.star(0), usage_array(), lit(unrestricted(t))) end
local function inf_typ(t, typ) return terms.inferrable_term.typed(unrestricted(t), usage_array(), typ) end
local inf_var = terms.inferrable_term.bound_variable
local function inf_lam(n, t, b) return terms.inferrable_term.annotated_lambda(n, inf_t(t), b) end
local inf_app = terms.inferrable_term.application

local t_num = terms.value.number_type
local i42 = inf_typ(t_num, n42)
local i69 = inf_typ(t_num, n69)
local i420 = inf_typ(t_num, n420)
local i621 = inf_typ(t_num, n621)
local i1337 = inf_typ(t_num, n1337)

local inf_id = inf_lam("x", t_num, inf_var(1))
local inf_const = inf_lam("val", t_num, inf_lam("ignored", t_num, inf_var(1)))

local apply_inf_id_with_42 = inf_app(inf_id, i42)
infer_and_eval("apply_inf_id_with_42", apply_inf_id_with_42)

local apply_inf_closure_with_capture = inf_app(inf_app(inf_const, i69), i1337)
infer_and_eval("apply_inf_closure_with_capture", apply_inf_closure_with_capture)

print("PART THREE!!!!!!!!")

local function inf_tup(...) return terms.inferrable_term.tuple_cons(inferrable_array(...)) end
local inf_tupelim = terms.inferrable_term.tuple_elim
local tuple_of_69_420 = inf_tup(i69, i420)
infer_and_eval("tuple_of_69_420", tuple_of_69_420)

local inf_swap = inf_tup(inf_var(2), inf_var(1))
local swap_69_420 = inf_tupelim(tuple_of_69_420, inf_swap)
infer_and_eval("swap_69_420", swap_69_420)

print("PART FOUR!!!!!!!!!")

local function prim_f(f) return lit(terms.value.prim(f)) end
local prim_add = prim_f(function(left, right) return left + right end)
local function prim_lit(x) return lit(terms.value.prim(x)) end
local function prim_tup(...) return terms.typed_term.prim_tuple_cons(typed_array(...)) end

local p69 = prim_lit(69)
local p420 = prim_lit(420)
local p621 = prim_lit(621)

local prim_add_69_420 = app(prim_add, prim_tup(p69, p420))
eval_test("prim_add_69_420", prim_add_69_420)

local function inf_prim_tup(...) return terms.inferrable_term.prim_tuple_cons(inferrable_array(...)) end

local t_prim_num = terms.value.prim_number_type
local ip69 = inf_typ(t_prim_num, p69)
local ip420 = inf_typ(t_prim_num, p420)
local ip621 = inf_typ(t_prim_num, p621)

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
local returns_input_and_3 = prim_f(function(a) return a, 3 end) -- returns_input_and_3(2) -> (2, 3)
local result = app(prim_add, app(returns_input_and_3, input)) -- add(2, 3) -> (5)
local t = terms.typed_term.tuple_elim(result, 1, primextractrepack) -- (5) -> (5, -1)
local result_2 = app(prim_add, t) -- add(5, -1) -> 4
local result_3 = terms.typed_term.tuple_elim(result_2, 1, var(1))
eval_test("repacking_tuples", result_3)

-- local fmt = require './format-adapter'
-- local user_defined_prim_a_id = { name = "syntax" }
-- local user_defined_prim_a_cons = terms.inferrable_term.prim_user_defined_type_cons(user_defined_prim_a_id, inferrable_array())
-- local value_user_defined_prim_a = infer_and_eval("syn_prim_cons", user_defined_prim_a_cons)

-- local prim_fmt_read = prim_f(function(str) return fmt.read(str, "inline") end)
-- local infer_prim_fmt_read = terms.inferrable_term.typed(value_user_defined_prim_a, usage_array(), terms.typed_term.literal(terms.value.prim(prim_fmt_read)))
-- infer_and_eval("user_defined_prim_syntax_cons", inf_app(infer_prim_fmt_read, terms.inferrable_term.typed(terms.value.prim_string_type, usage_array(), prim_lit("+ 2 3"))))


print("PART SIX!!!!!!!!!!")

local value_array = array(terms.value)
local function tup_val(...) return terms.value.tuple_value(value_array(...)) end
local function cons(...) return terms.value.data_value("cons", tup_val(...)) end
local empty = terms.value.data_value("empty", tup_val())
local function ctype(t)
  local initial_context = terms.runtime_context()
  return eval.evaluate(app(const, lit(t)), initial_context)
end
local tuple_decl = unrestricted(terms.value.prim_tuple_type(
  cons(
    cons(
      empty,
      ctype(unrestricted(t_prim_num))
    ),
    ctype(unrestricted(t_prim_num))
  )
))
local mogrify = prim_f(function(left, right) return left + right, left - right end)
local inf_mogrify = inf_typ(terms.value.prim_function_type(tuple_decl, tuple_decl), mogrify)
local apply_mogrify_with_621_420 = inf_app(inf_mogrify, tuple_of_621_420)
infer_and_eval("apply_mogrify_with_621_420", apply_mogrify_with_621_420)
