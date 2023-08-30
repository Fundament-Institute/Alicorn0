local gen = require './terms-generators'
local terms = require './terms'
local eval = require './evaluator'

print("PART ONE!!!!!!!!!!")

local function lit(x) return terms.typed_term.literal(terms.value.number(x)) end
local var = terms.typed_term.bound_variable
local lam = terms.typed_term.lambda
local app = terms.typed_term.application

local initial_context = terms.runtime_context()
local result

-- var(1) refers to the outermost bound variable, 2 next outermost, etc
-- as opposed to de bruijn indices, where 1 refers to the innermost (nearest) binding, etc
local id = lam(var(1))
local const = lam(lam(var(1)))
-- in de bruijn indices, these would be lam(var(1)) and lam(lam(var(2))) respectively

local apply_id_with_42 = app(id, lit(42))
result = eval.evaluate(apply_id_with_42, initial_context)
p(result)
assert(result.kind == "value_number" and result.number == 42)

local apply_closure_with_capture = app(app(const, lit(69)), lit(1337))
result = eval.evaluate(apply_closure_with_capture, initial_context)
p(result)
assert(result.kind == "value_number" and result.number == 69)

print("PART TWO!!!!!!!!!!")

local array = gen.declare_array
local usage_array = array(gen.builtin_number)

local unrestricted_number_type = terms.value.qtype(terms.value.quantity(terms.quantity.unrestricted), terms.value.number_type)
local inf_unrestricted_number_type = terms.inferrable_term.typed(terms.value.star(0), usage_array(), terms.typed_term.literal(unrestricted_number_type))

local function inflit(x) return terms.inferrable_term.typed(unrestricted_number_type, usage_array(), lit(x)) end
local infvar = terms.inferrable_term.bound_variable
local function inflam(b) return terms.inferrable_term.annotated_lambda(inf_unrestricted_number_type, b) end
local infapp = terms.inferrable_term.application

local initial_typechecking_context = terms.typechecking_context()
local result_type, result_usages, result_term

local infid = inflam(infvar(1))
local infconst = inflam(inflam(infvar(1)))

local apply_infid_with_42 = infapp(infid, inflit(42))
result_type, result_usages, result_term = eval.infer(apply_infid_with_42, initial_typechecking_context)
p(result_type)
p(result_usages)
p(result_term)
result = eval.evaluate(result_term, initial_context)
p(result)

local apply_inf_closure_with_capture = infapp(infapp(infconst, inflit(69)), inflit(1337))
result_type, result_usages, result_term = eval.infer(apply_inf_closure_with_capture, initial_typechecking_context)
p(result_type)
p(result_usages)
p(result_term)
result = eval.evaluate(result_term, initial_context)
p(result)
