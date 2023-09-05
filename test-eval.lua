local gen = require './terms-generators'
local terms = require './terms'
local eval = require './evaluator'

print("PART ONE!!!!!!!!!!")

local function eval_test(name, term)
  local initial_context = terms.runtime_context()
  print("test: " .. name)
  local result = eval.evaluate(term, initial_context)
  p("result", result)
  return result
end

local function lit(x) return terms.typed_term.literal(terms.value.number(x)) end
local var = terms.typed_term.bound_variable
local lam = terms.typed_term.lambda
local app = terms.typed_term.application

-- var(1) refers to the outermost bound variable, 2 next outermost, etc
-- as opposed to de bruijn indices, where 1 refers to the innermost (nearest) binding, etc
local id = lam(var(1))
local const = lam(lam(var(1)))
-- in de bruijn indices, these would be lam(var(1)) and lam(lam(var(2))) respectively

local result

local apply_id_with_42 = app(id, lit(42))
result = eval_test("apply_id_with_42", apply_id_with_42)
assert(result.kind == "value_number" and result.number == 42)

local apply_closure_with_capture = app(app(const, lit(69)), lit(1337))
result = eval_test("apply_closure_with_capture", apply_closure_with_capture)
assert(result.kind == "value_number" and result.number == 69)

print("PART TWO!!!!!!!!!!")

local function infer_and_eval(name, inf)
  local initial_context = terms.runtime_context()
  local initial_typechecking_context = terms.typechecking_context()
  print("test: " .. name)
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

local unrestricted_number_type = terms.value.qtype(terms.value.quantity(terms.quantity.unrestricted), terms.value.number_type)
local inf_unrestricted_number_type = terms.inferrable_term.typed(terms.value.star(0), usage_array(), terms.typed_term.literal(unrestricted_number_type))

local function inflit(x) return terms.inferrable_term.typed(unrestricted_number_type, usage_array(), lit(x)) end
local infvar = terms.inferrable_term.bound_variable
local function inflam(b) return terms.inferrable_term.annotated_lambda("the_param", inf_unrestricted_number_type, b) end
local infapp = terms.inferrable_term.application

local infid = inflam(infvar(1))
local infconst = inflam(inflam(infvar(1)))

local apply_infid_with_42 = infapp(infid, inflit(42))
infer_and_eval("apply_infid_with_42", apply_infid_with_42)

local apply_inf_closure_with_capture = infapp(infapp(infconst, inflit(69)), inflit(1337))
infer_and_eval("apply_inf_closure_with_capture", apply_inf_closure_with_capture)

print("PART THREE!!!!!!!!")

local function inflitty(ty, lit_val)
  return terms.inferrable_term.typed(
    terms.value.qtype(terms.value.quantity(terms.quantity.unrestricted)),
    usage_array(),
    terms.typed_term.literal(lit_val)
  )
end

local function infprimtup(...) return terms.inferrable_term.prim_tuple_cons(inferrable_array(...)) end
local function inftup(...) return terms.inferrable_term.tuple_cons(inferrable_array(...)) end
local tuple_of_69_420 = inftup(inflit(69), inflit(420))
infer_and_eval("tuple_of_69_420", tuple_of_69_420)

local function mechalam(b) return terms.mechanism_term.lambda("the_param", b) end
local mechainf = terms.mechanism_term.inferrable
local infswap = mechalam(mechalam(mechainf(inftup(infvar(2), infvar(1)))))
local swap_69_420 = terms.inferrable_term.tuple_elim(infswap, tuple_of_69_420)
infer_and_eval("swap_69_420", swap_69_420)

print("PART FOUR!!!!!!!!!")

local function prim_f(f) return terms.typed_term.literal(terms.value.prim(f)) end
local prim_add = prim_f(function(left, right) return left + right end)
local function prim_lit(x) return terms.typed_term.literal(terms.value.prim(x)) end
local function prim_tup(...) return terms.typed_term.prim_tuple_cons(typed_array(...)) end
local prim_add_69_420 = app(prim_add, prim_tup(prim_lit(69), prim_lit(420)))
eval_test("prim_add_69_420", prim_add_69_420)

local infprimswap = mechalam(mechalam(mechainf(infprimtup(infvar(2), infvar(1)))))
local inf_prim_tuple_of_621_420 = infprimtup(inflit(621), inflit(420))
local inf_swap_prim_621_420 = terms.inferrable_term.tuple_elim(infprimswap, inf_prim_tuple_of_621_420)
infer_and_eval("swap_prim_621_420", inf_swap_prim_621_420)

print("prim tuple elim test")

local function typedvar(x) return terms.typed_term.bound_variable(x) end
local primextractrepack = lam(prim_tup(typedvar(1), prim_lit(-1)))

-- create prim tuple
-- call prim function
-- use tuple elim to extract results and repack with another prim
-- call another primitive function

local input = prim_tup(prim_lit(2)) -- -> (2)
local returns_input_and_3 = prim_f(function(a) return a, 3 end) -- returns_input_and_3(2) -> (2, 3)
local result = app(prim_add, app(returns_input_and_3, input)) -- add(2, 3) -> (5)
local t = terms.typed_term.tuple_elim(primextractrepack, result) -- (5) -> (5, -1)
local result_2 = app(prim_add, t) -- add(5, -1) -> 4
local result_3 = terms.typed_term.tuple_elim(lam(typedvar(1)), result_2)
eval_test("repacking_tuples", result_3)

-- local fmt = require './format-adapter'
-- local user_defined_prim_a_id = { name = "syntax" }
-- local user_defined_prim_a_cons = terms.inferrable_term.prim_user_defined_type_cons(user_defined_prim_a_id, inferrable_array())
-- local value_user_defined_prim_a = infer_and_eval("syn_prim_cons", user_defined_prim_a_cons)

-- local prim_fmt_read = prim_f(function(str) return fmt.read(str, "inline") end)
-- local infer_prim_fmt_read = terms.inferrable_term.typed(value_user_defined_prim_a, usage_array(), terms.typed_term.literal(terms.value.prim(prim_fmt_read)))
-- infer_and_eval("user_defined_prim_syntax_cons", infapp(infer_prim_fmt_read, terms.inferrable_term.typed(terms.value.prim_string_type, usage_array(), prim_lit("+ 2 3"))))

