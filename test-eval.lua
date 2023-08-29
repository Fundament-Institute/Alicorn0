local terms = require './terms'
local environment = require './environment'

local typed_literal_42 = terms.typed_term.literal(terms.value.number(42))
local typed_id = terms.typed_term.lambda(terms.typed_term.bound_variable(0))
local apply_id_with_42 = terms.typed_term.application(typed_id, typed_literal_42)
local initial_context = environment.runtime_context()
local result = terms.evaluate(apply_id_with_42, initial_context)
p(result)
assert(result.kind == "value_number" and result.number == 42)
