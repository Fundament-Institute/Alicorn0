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

--[[
-- Evaluator cases for levels use non-existent flex_value.level_type and flex_value.level
function test_levels()
	print(unanchored_inferrable_term.level0)
	local suc_term = anchored_inferrable_term(
		format.anchor_here(),
		unanchored_inferrable_term.level_suc(
			anchored_inferrable_term(format.anchor_here(), unanchored_inferrable_term.level0)
		)
	)
	print(suc_term)
	local test_term = anchored_inferrable_term(
		format.anchor_here(),
		unanchored_inferrable_term.level_max(
			suc_term,
			anchored_inferrable_term(format.anchor_here(), unanchored_inferrable_term.level0)
		)
	)
	local ok, inferred_type, usages, typed_term = infer(test_term, tc)
	p(inferred_type)
	assert(inferred_type:is_level_type())
	local result = evaluate(typed_term, rc)
	p(result)
	assert(result:is_level())
	assert(result:unwrap_level() == 1)
	assert(result.level == 1)
end

-- unanchored_inferrable_term.star doesn't exist
function test_star()
	local test_term = anchored_inferrable_term(format.anchor_here(), unanchored_inferrable_term.star)
	local ok, inferred_type, inferred_term = infer(test_term, tc)
	p(inferred_type, inferred_term)
	assert(inferred_type.kind == "value_star")
	local result = evaluate(inferred_term, rc)
	p(result)
	assert(result.kind == "value_star")
	assert(result.level == 0)
end
]]

test_empty_tuple()
