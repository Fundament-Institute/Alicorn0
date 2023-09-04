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

local function inftup(...) return terms.inferrable_term.tuple_cons(array(terms.inferrable_term)(...)) end
local tuple_of_69_420 = inftup(inflit(69), inflit(420))
infer_and_eval("tuple_of_69_420", tuple_of_69_420)

local function mechalam(b) return terms.mechanism_term.lambda("the_param", b) end
local mechainf = terms.mechanism_term.inferrable
local infswap = mechalam(mechalam(mechainf(inftup(infvar(2), infvar(1)))))
local swap_69_420 = terms.inferrable_term.tuple_elim(infswap, tuple_of_69_420)
infer_and_eval("swap_69_420", swap_69_420)

print("PART FOUR!!!!!!!!!")

local prim_add = value.prim(function(left, right) return left + right end)
local prim_ = typed_term.literal.prim
