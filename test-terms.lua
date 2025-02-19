local terms = require "terms"
local evaluator = require "evaluator"
local unanchored_inferrable_term = terms.unanchored_inferrable_term
local anchored_inferrable_term = terms.anchored_inferrable_term
local format = require "format"
local infer = evaluator.infer
local evaluate = evaluator.evaluate
local tc = terms.typechecking_context()
local rc = tc.runtime_context
local anchored_inferrable_term, anchored_inferrable_term_array =
	terms.anchored_inferrable_term, terms.anchored_inferrable_term_array
local spanned_name, spanned_name_array = terms.spanned_name, terms.spanned_name_array

local function test_empty_tuple()
	local tuple_term = anchored_inferrable_term(
		format.anchor_here(),
		unanchored_inferrable_term.tuple_cons(anchored_inferrable_term_array(), spanned_name_array())
	)
	local ok, inferred_type, usages, typed_term = infer(tuple_term, tc)
	p("Empty tuple inferred type and typed term:", inferred_type, typed_term)
	assert(inferred_type:is_tuple_type())
	local result = evaluate(typed_term, rc)
	p("Empty tuple evaluated to:", result)
	assert(result:is_tuple_value())
	assert(#result:unwrap_tuple_value() == 0)
	print("test_empty_tuple success")
end

test_empty_tuple()
