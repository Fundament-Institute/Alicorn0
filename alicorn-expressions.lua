-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

-- get new version of let and do working with terms

local metalanguage = require "metalanguage"

local format = require "format"
local Anchor = format.create_anchor
local terms = require "terms"
local expression_goal = terms.expression_goal
--local typechecking_context = terms.typechecking_context
local checkable_term = terms.checkable_term
local unanchored_inferrable_term = terms.unanchored_inferrable_term
local anchored_inferrable_term, anchored_inferrable_term_array =
	terms.anchored_inferrable_term, terms.anchored_inferrable_term_array
local typed_term, typed_term_array = terms.typed_term, terms.typed_term_array
local visibility = terms.visibility
local purity = terms.purity
local result_info = terms.result_info
local flex_value = terms.flex_value
local strict_value, strict_value_array = terms.strict_value, terms.strict_value_array
local spanned_name, spanned_name_array = terms.spanned_name, terms.spanned_name_array
--local host_syntax_type = terms.host_syntax_type
--local host_environment_type = terms.host_environment_type
--local host_inferrable_term_type = terms.host_inferrable_term_type

local gen = require "terms-generators"
local array = gen.declare_array
--local checkable_array = array(checkable_term)
local usage_array = array(gen.builtin_integer)
local name_array = array(gen.builtin_string)

local param_info_implicit = strict_value.param_info(strict_value.visibility(visibility.implicit))
local param_info_explicit = strict_value.param_info(strict_value.visibility(visibility.explicit))
local result_info_pure = strict_value.result_info(result_info(purity.pure))
local result_info_effectful = strict_value.result_info(result_info(purity.effectful))

local empty_tuple = terms.strict_value.tuple_value(strict_value_array())

local evaluator = require "evaluator"
local const_combinator = evaluator.const_combinator
local infer = evaluator.infer
-- BUG: do not uncomment this, as speculation relies on changing evaluator.typechecking_state, which is masked by the local
--local typechecker_state = evaluator.typechecker_state

local U = require "alicorn-utils"

---@class SemanticErrorData
---@field text string
---@field cause any
---@field spans Span[]?
---@field terms { [string]: table }?
---@field env Environment?

local semantic_error_mt = {
	---@param self SemanticErrorData
	---@return unknown
	__tostring = function(self)
		local message = { self.text }
		if self.spans then
			message[#message + 1] = " at spans"
			for _, span in ipairs(self.spans) do
				message[#message], message[#message + 1], message[#message + 2], message[#message + 3] =
					" ", message[#message], " ", tostring(span)
			end
		end
		if self.terms then
			message[#message + 1] = " with terms\n"
			for k, term in pairs(self.terms) do
				local s = nil
				if term.pretty_print and self.env then
					s = term:pretty_print(self.env.typechecking_context) --[[@as string]]
				else
					s = tostring(term)
				end
				message[#message + 1], message[#message + 2], message[#message + 3], message[#message + 4] =
					k, " = ", s, "\n"
			end
		end
		if self.env then
			message[#message + 1] = " in env\n"
			message[#message + 1], message[#message + 2] = self.env.typechecking_context:format_names(), "\n"
		end
		if self.cause then
			message[#message + 1], message[#message + 2] = " because:\n", tostring(self.cause)
		end
		return table.concat(message, "")
	end,
}

local semantic_error = {
	---@param cause any
	---@return SemanticErrorData
	function_args_mismatch = function(cause)
		return {
			text = "function args mismatch",
			cause = cause,
		}
	end,
	-- ---@param t any
	-- non_operable_combiner = function(t)
	-- 	return {
	-- 		text = "value in combiner slot that can't operate of type " .. types.type_name(t),
	-- 	}
	-- end,
	---@param cause any
	---@param spans Span[]
	---@return SemanticErrorData
	operative_apply_failed = function(cause, spans)
		return {
			text = "operative apply failed",
			cause = cause,
			spans = spans,
		}
	end,

	---@param cause any
	---@param spans Span[]
	---@param terms { [string]: table }
	---@param env Environment
	---@return SemanticErrorData
	host_function_argument_collect_failed = function(cause, spans, terms, env)
		return {
			text = "host_function_argument_collect_failed",
			cause = cause,
			spans = spans,
			terms = terms,
			env = env,
		}
	end,
}

for k, v in pairs(semantic_error) do
	semantic_error[k] = function(...)
		return setmetatable(v(...), semantic_error_mt)
	end
end

local expression
local collect_tuple
local collect_host_tuple

---@class ExpressionArgs
---@field goal expression_goal
---@field env Environment
local ExpressionArgs = {}

---@class TopLevelBlockArgs
---@field exprargs ExpressionArgs
---@field name string
local TopLevelBlockArgs = {}

---Unpack ExpressionArgs into component parts
---@return expression_goal
---@return Environment
function ExpressionArgs:unwrap()
	return self.goal, self.env
end

---@param goal expression_goal
---@param env Environment
---@return ExpressionArgs
function ExpressionArgs.new(goal, env)
	if not goal then
		error("missing or incorrect goal passed to expression_args")
	end
	if not env or not env.get then
		error("missing or incorrect env passed to expression_args")
	end
	return setmetatable({
		goal = goal,
		env = env,
	}, { __index = ExpressionArgs })
end

-- work around lua lsp not warning about invalid enum accesses
---@class OperatorTypeContainer
local OperatorType = --[[@enum OperatorType]]
	{
		Prefix = "Prefix",
		Infix = "Infix",
	}

---@class (exact) PrefixData

---@type {[string]: PrefixData}
local prefix_data = {
	["-"] = {},
	["@"] = {},
}

---@class AssociativityContainer
local Associativity = --[[@enum Associativity]]
	{
		r = "r",
		l = "l",
	}

---@class (exact) InfixData
---@field precedence integer
---@field associativity Associativity

---@type {[string]: InfixData}
local infix_data = {
	["="] = { precedence = 2, associativity = "r" },
	["|"] = { precedence = 3, associativity = "l" },
	["&"] = { precedence = 3, associativity = "l" },
	["!"] = { precedence = 3, associativity = "l" },
	["<"] = { precedence = 4, associativity = "l" },
	[">"] = { precedence = 4, associativity = "l" },
	["+"] = { precedence = 5, associativity = "l" },
	["-"] = { precedence = 5, associativity = "l" },
	["*"] = { precedence = 6, associativity = "l" },
	["/"] = { precedence = 6, associativity = "l" },
	["%"] = { precedence = 6, associativity = "l" },
	["^"] = { precedence = 7, associativity = "r" },
	[":"] = { precedence = 8, associativity = "l" },
	-- # is the comment character and is forbidden here
}

---@param symbol SyntaxSymbol
---@return boolean
---@return SyntaxSymbol | string
local function shunting_yard_prefix_handler(_, symbol)
	assert(symbol and symbol["kind"])

	if not prefix_data[(symbol.str):sub(1, 1)] or (symbol.str):find("_") then
		return false,
			"symbol was provided in a prefix operator place, but the symbol isn't a valid prefix operator: "
				.. symbol.str
	end
	return true, symbol
end

---@param symbol SyntaxSymbol
---@param a ConstructedSyntax
---@param b ConstructedSyntax
---@return boolean
---@return boolean|string
---@return SyntaxSymbol?
---@return ConstructedSyntax?
---@return ConstructedSyntax?
local function shunting_yard_infix_handler(_, symbol, a, b)
	assert(symbol and symbol["kind"])
	if not infix_data[(symbol.str):sub(1, 1)] or (symbol.str):find("_") then
		return false,
			"symbol was provided in an infix operator place, but the symbol isn't a valid infix operator: "
				.. symbol.str
	end
	return true, true, symbol, a, b
end

---@return boolean
---@return boolean
local function shunting_yard_nil_handler(_)
	return true, false
end

---@class (exact) TaggedOperator
---@field type OperatorType
---@field symbol SyntaxSymbol

---@param yard { n: integer, [integer]: TaggedOperator }
---@param output { n: integer, [integer]: ConstructedSyntax }
---@param span Span
local function shunting_yard_pop(yard, output, span)
	local yard_height = yard.n
	local output_length = output.n
	local operator = yard[yard_height]
	local operator_type = operator.type
	local operator_symbol = operator.symbol
	if operator_type == OperatorType.Prefix then
		local arg = output[output_length]
		local tree = metalanguage.list(span, metalanguage.symbol(span, operator_symbol), arg)
		yard[yard_height] = nil
		yard.n = yard_height - 1
		output[output_length] = tree
	elseif operator_type == OperatorType.Infix then
		local right = output[output_length]
		local left = output[output_length - 1]
		local tree = metalanguage.list(span, left, metalanguage.symbol(span, operator_symbol), right)
		yard[yard_height] = nil
		yard.n = yard_height - 1
		output[output_length] = nil
		output[output_length - 1] = tree
		output.n = output_length - 1
	else
		error("unknown operator type")
	end
end

---@param new_symbol SyntaxSymbol
---@param yard_operator TaggedOperator
---@return boolean
local function shunting_yard_should_pop(new_symbol, yard_operator)
	assert(new_symbol and new_symbol["kind"])

	-- new_symbol is always infix, as we never pop while adding a prefix operator
	-- prefix operators always have higher precedence than infix operators
	local yard_type = yard_operator.type
	if yard_type == OperatorType.Prefix then
		return true
	end
	if yard_type ~= OperatorType.Infix then
		error("unknown operator type")
	end
	local yard_symbol = yard_operator.symbol
	local new_data = infix_data[(new_symbol.str):sub(1, 1)]
	local yard_data = infix_data[(yard_symbol.str):sub(1, 1)]
	local new_precedence = new_data.precedence
	local yard_precedence = yard_data.precedence
	if new_precedence < yard_precedence then
		return true
	end
	if new_precedence > yard_precedence then
		return false
	end
	local new_associativity = new_data.associativity
	local yard_associativity = yard_data.associativity
	if new_associativity ~= yard_associativity then
		-- if you actually hit this error, it's because the infix_data is badly specified
		-- one of the precedence levels has both left- and right-associative operators
		-- please separate these operators into different precedence levels to disambiguate
		error("clashing associativities!!!")
	end
	if new_associativity == Associativity.l then
		return true
	end
	if new_associativity == Associativity.r then
		return false
	end
	error("unknown associativity")
end

---@param a ConstructedSyntax
---@param b ConstructedSyntax
---@param yard { n: integer, [integer]: TaggedOperator }
---@param output { n: integer, [integer]: ConstructedSyntax }
---@param span Span
---@return boolean
---@return ConstructedSyntax|string
local function shunting_yard(a, b, yard, output, span)
	-- first, collect all prefix operators
	local is_prefix, prefix_symbol =
		a:match({ metalanguage.issymbol(shunting_yard_prefix_handler) }, metalanguage.failure_handler, nil)
	---@cast prefix_symbol SyntaxSymbol
	if is_prefix then
		local ok, next_a, next_b =
			b:match({ metalanguage.ispair(metalanguage.accept_handler) }, metalanguage.failure_handler, nil)
		if not ok then
			return ok, next_a
		end
		-- prefix operators always have higher precedence than infix operators,
		-- all have the same precedence as each other (conceptually), and are always right-associative
		-- this means we never need to pop the yard before adding a prefix operator to it
		yard.n = yard.n + 1
		yard[yard.n] = {
			type = OperatorType.Prefix,
			symbol = prefix_symbol,
		}
		return shunting_yard(next_a, next_b, yard, output, span)
	end
	-- no more prefix operators, now handle infix
	output.n = output.n + 1
	output[output.n] = a
	local ok, more, infix_symbol, next_a, next_b = b:match({
		metalanguage.listtail(
			shunting_yard_infix_handler,
			metalanguage.issymbol(metalanguage.accept_handler),
			metalanguage.any(metalanguage.accept_handler)
		),
		metalanguage.isnil(shunting_yard_nil_handler),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, more
	end
	if infix_symbol then
		assert(infix_symbol["kind"])
	end
	if not more then
		while yard.n > 0 do
			shunting_yard_pop(yard, output, span)
		end
		return true, output[1]
	end
	while yard.n > 0 and shunting_yard_should_pop(infix_symbol, yard[yard.n]) do
		shunting_yard_pop(yard, output, span)
	end
	yard.n = yard.n + 1
	yard[yard.n] = {
		type = OperatorType.Infix,
		symbol = infix_symbol,
	}
	return shunting_yard(next_a, next_b, yard, output, span)
end

---@param symbol SyntaxSymbol
---@param arg ConstructedSyntax
---@return boolean
---@return OperatorType|string
---@return string?
---@return ConstructedSyntax?
local function expression_prefix_handler(_, symbol, arg)
	if not prefix_data[(symbol.str):sub(1, 1)] or (symbol.str):find("_") then
		return false,
			"symbol was provided in a prefix operator place, but the symbol isn't a valid prefix operator: "
				.. tostring(symbol)
	end
	return true, OperatorType.Prefix, symbol.str, arg
end

---@param left ConstructedSyntax
---@param symbol SyntaxSymbol
---@param right ConstructedSyntax
---@return boolean
---@return OperatorType|string
---@return string?
---@return ConstructedSyntax?
---@return ConstructedSyntax?
local function expression_infix_handler(_, left, symbol, right)
	assert(symbol and symbol["kind"])

	if not infix_data[(symbol.str):sub(1, 1)] or (symbol.str):find("_") then
		return false,
			"symbol was provided in an infix operator place, but the symbol isn't a valid infix operator: " .. tostring(
				symbol
			)
	end
	return true, OperatorType.Infix, symbol.str, left, right
end

---@overload fun() : boolean, string
---@param env Environment
---@param metaval flex_value
---@return boolean, flex_value
local function speculate_pi_type(env, metaval)
	-- FIXME: There is a way to avoid this combinatoric explosion that nobody has properly explained yet. If this gets too big, we need to do it properly.
	local pairs = {
		{ param_info = param_info_implicit, result_info = result_info_pure },
		{ param_info = param_info_explicit, result_info = result_info_pure },
		{ param_info = param_info_implicit, result_info = result_info_effectful },
		{ param_info = param_info_explicit, result_info = result_info_effectful },
	}

	local ok, res
	for i = 1, 4 do
		ok, res = evaluator.typechecker_state:speculate(function()
			local param_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
			local result_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
			local pi = terms.flex_value.pi(
				terms.flex_value.stuck(param_mv:as_stuck()),
				flex_value.strict(pairs[i].param_info),
				terms.flex_value.stuck(result_mv:as_stuck()),
				flex_value.strict(pairs[i].result_info)
			)

			local ok, err = evaluator.typechecker_state:flow(
				metaval,
				env.typechecking_context,
				pi,
				env.typechecking_context,
				terms.constraintcause.primitive("Speculating on pi type", format.anchor_here())
			)
			if not ok then
				---@cast err -nil
				return false, err
			end

			return true, pi
		end)

		if ok then
			---@cast res -nil
			return ok, res
		end
	end

	---@cast res -nil
	return ok, res
end

---HORRIBLE HACK MAKE THIS BETTER
---@overload fun() : boolean, string
---@param env Environment
---@param metaval flex_value
---@return boolean, flex_value
local function operative_test_hack(env, metaval)
	if
		metaval:is_stuck()
		and metaval:unwrap_stuck():is_free()
		and metaval:unwrap_stuck():unwrap_free():is_metavariable()
	then
		local mv = metaval:unwrap_stuck():unwrap_free():unwrap_metavariable()
		local edges = evaluator.typechecker_state.graph.constrain_edges:to(mv.usage)
		local res = nil
		for _, edge in ipairs(edges) do
			if res then
				return false, "too many edges, couldn't pick one"
			end
			if edge.rel ~= evaluator.UniverseOmegaRelation then
				return false, "not a subtyping relation"
			end
			res = evaluator.typechecker_state.values[edge.left][1]
		end
		return true, res
	elseif
		metaval:is_stuck()
		and metaval:unwrap_stuck():is_application()
		and metaval:unwrap_stuck():unwrap_application():is_free()
		and metaval:unwrap_stuck():unwrap_application():unwrap_free():is_metavariable()
	then
		local stuck_f, arg = metaval:unwrap_stuck():unwrap_application()
		local mv = stuck_f:unwrap_free():unwrap_metavariable()
		local edges = evaluator.typechecker_state.graph.constrain_edges:to(mv.usage)
		local f = nil
		for _, edge in ipairs(edges) do
			if f then
				return false, "too many edges, couldn't pick one"
			end
			if edge.rel ~= evaluator.FunctionRelation(evaluator.UniverseOmegaRelation) then
				return false, "not a func(subtyping) relation"
			end
			f = evaluator.typechecker_state.values[edge.left][1]
		end
		if terms.flex_value.value_check(f) ~= true then
			return false, "idk what this is but it ain't an operative"
		end
		local res = evaluator.apply_value(f, arg, env.typechecking_context)
		return true, res
	else
		return true, metaval
	end
end

---@param start_anchor Anchor
---@param type_of_term flex_value
---@param usage_count ArrayValue<integer>
---@param term typed
---@param sargs ConstructedSyntax syntax arguments
---@param goal expression_goal
---@param env Environment
---@return tristate
---@return (string|checkable|anchored_inferrable|flex_value)
---@return Environment?
local function call_operative(start_anchor, type_of_term, usage_count, term, sargs, goal, env)
	-- TODO: speculate operative type
	local ok
	ok, type_of_term = operative_test_hack(env, type_of_term)
	if not ok then
		return terms.tristate.continue, type_of_term
	end
	local is_op, handler, userdata_type = type_of_term:as_operative_type()
	if not is_op then
		return terms.tristate.continue, "not an operative"
	end

	-- operative input: env, syntax tree, goal type (if checked)
	local tuple_args = strict_value_array(
		strict_value.host_value(sargs),
		strict_value.host_value(env),
		strict_value.host_value(term),
		strict_value.host_value(goal)
	)

	local operative_result_val = evaluator.apply_value(
		handler,
		terms.flex_value.strict(terms.strict_value.tuple_value(tuple_args)),
		env.typechecking_context
	)
	-- result should be able to be an inferred term, can fail
	-- NYI: operative_cons in evaluator must use Maybe type once it exists
	-- if not operative_result_val:is_enum_value() then
	-- 	p(operative_result_val.kind)
	-- 	print(operative_result_val:pretty_print())
	-- 	return false, "applying operative did not result in value term with kind enum_value, typechecker or lua operative mistake when applying " .. tostring(a.start_anchor) .. " to the args " .. tostring(b.start_anchor)
	-- end
	-- variants: ok, error
	--if operative_result_val.variant == "error" then
	--	return false, semantic_error.operative_apply_failed(operative_result_val.data, { a.start_anchor, b.start_anchor })
	--end

	-- temporary, while it isn't a Maybe
	if not operative_result_val:is_tuple_value() then
		print("bad operative?", handler)
		print("bad result val", operative_result_val)
		error "operative handler didn't complete properly"
	end
	local operative_result_elems = operative_result_val:unwrap_tuple_value()
	local data = operative_result_elems[1]:unwrap_host_value()
	local env = operative_result_elems[2]:unwrap_host_value()
	--if not env then
	--	print("operative_result_val.elements[2]", operative_result_val.elements[2]:pretty_print())
	--	error "operative_result_val missing env"
	--end

	if goal:is_check() then
		local checkable = data
		local goal_type = goal:unwrap_check()
		local ok, usage_counts, term = evaluator.check(checkable, env.typechecking_context, goal_type)
		if not ok then
			return terms.tristate.failure, usage_counts
		end
		return terms.tristate.success,
			U.notail(
				checkable_term.inferrable(
					anchored_inferrable_term(
						start_anchor,
						unanchored_inferrable_term.typed(
							evaluator.substitute_placeholders_identity(goal_type, env.typechecking_context),
							usage_counts,
							term
						)
					)
				)
			),
			env
	elseif goal:is_infer() then
		local ok, resulting_type, usage_counts, term = infer(data, env.typechecking_context)
		if not ok then
			return terms.tristate.failure, resulting_type
		end
		return terms.tristate.success,
			U.notail(
				anchored_inferrable_term(
					start_anchor,
					unanchored_inferrable_term.typed(
						evaluator.substitute_placeholders_identity(resulting_type, env.typechecking_context),
						usage_counts,
						term
					)
				)
			),
			env
	else
		error("NYI goal " .. goal.kind .. " for operative in expression_pairhandler")
	end
end

---@param start_anchor Anchor
---@param type_of_term flex_value
---@param usage_count ArrayValue<integer>
---@param term typed
---@param sargs ConstructedSyntax
---@param goal expression_goal
---@param env Environment
---@return tristate
---@return string|checkable|anchored_inferrable|flex_value
---@return Environment?
local function call_pi(start_anchor, type_of_term, usage_count, term, sargs, goal, env)
	local ok
	ok, type_of_term = speculate_pi_type(env, type_of_term)
	if not ok then
		return terms.tristate.continue, type_of_term
	end

	local param_type, param_info, result_type, result_info = type_of_term:unwrap_pi()

	local overflow = 0
	while param_info:unwrap_param_info():unwrap_visibility():is_implicit() do
		overflow = overflow + 1
		if overflow > 1024 then
			error("Either you have a parameter with more than 1024 implicit parameters or this is an infinite loop!")
		end

		local metavar = evaluator.typechecker_state:metavariable(env.typechecking_context)
		local metaresult = evaluator.apply_value(result_type, metavar:as_flex(), env.typechecking_context)
		local ok, inner_pi = speculate_pi_type(env, metaresult)

		if not ok then
			error(
				"calling function with implicit args, result type applied on implicit args must be a function type: "
					.. metaresult:pretty_print(env.typechecking_context)
					.. "\n\n@@@tb1@@@\n\n"
					.. tostring(inner_pi)
					.. "\n\n@@@tb2@@@"
			)
		end

		term = typed_term.application(term, terms.typed_term.metavariable(metavar))
		type_of_term = inner_pi
		param_type, param_info, result_type, result_info = inner_pi:unwrap_pi()
	end

	---@type boolean, checkable|string, Environment
	local ok, tuple, env = sargs:match({
		collect_tuple(metalanguage.accept_handler, ExpressionArgs.new(expression_goal.check(param_type), env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		-- TODO: semantic error? like call_host_func_type
		error(tuple)
	end
	---@cast tuple checkable

	---@type string | anchored_inferrable | checkable
	local res = anchored_inferrable_term(
		start_anchor,
		unanchored_inferrable_term.application(

			anchored_inferrable_term(
				start_anchor,
				unanchored_inferrable_term.typed(
					evaluator.substitute_placeholders_identity(type_of_term, env.typechecking_context),
					usage_count,
					term
				)
			),
			tuple
		)
	)
	---@cast res anchored_inferrable

	if result_info:unwrap_result_info():unwrap_result_info():is_effectful() then
		local bind = terms.binding.program_sequence(res, sargs.span.start)
		ok, env = env:bind_local(bind)
		if not ok then
			return terms.tristate.failure, env
		end
		ok, res = env:get("#program-sequence") --TODO refactor
		if not ok then
			error(res)
		end
	end

	if goal:is_check() then
		res = checkable_term.inferrable(res)
	end

	return terms.tristate.success, res, env
end

---@param start_anchor Anchor
---@param type_of_term_input flex_value
---@param usage_count ArrayValue<integer>
---@param term typed
---@param sargs ConstructedSyntax
---@param goal expression_goal
---@param env Environment
---@return tristate
---@return string|checkable|anchored_inferrable
---@return Environment?
local function call_host_func_type(start_anchor, type_of_term_input, usage_count, term, sargs, goal, env)
	local ok, type_of_term = evaluator.typechecker_state:speculate(function()
		local param_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
		local result_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
		local host_func_type =
			flex_value.host_function_type(param_mv:as_flex(), result_mv:as_flex(), flex_value.strict(result_info_pure))

		local ok, err = evaluator.typechecker_state:flow(
			type_of_term_input,
			env.typechecking_context,
			host_func_type,
			env.typechecking_context,
			terms.constraintcause.primitive("Speculating on host func type", format.anchor_here())
		)
		if not ok then
			return false, err
		end

		return true, host_func_type
	end)
	if not ok then
		-- FIXME: Do this correctly instead of just guessing the other purity option
		ok, type_of_term = evaluator.typechecker_state:speculate(function()
			local param_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
			local result_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
			local host_func_type = flex_value.host_function_type(
				param_mv:as_flex(),
				result_mv:as_flex(),
				flex_value.strict(result_info_effectful)
			)

			local ok, err = evaluator.typechecker_state:flow(
				type_of_term_input,
				env.typechecking_context,
				host_func_type,
				env.typechecking_context,
				terms.constraintcause.primitive("Speculating on host func type", format.anchor_here())
			)

			if not ok then
				return false, err
			end

			return true, host_func_type
		end)

		if not ok then
			--print("ERRORED:", type_of_term)
			---@cast type_of_term string
			return terms.tristate.continue, type_of_term
		end
		---@cast type_of_term -string
	end

	local param_type, result_type, result_info = type_of_term:unwrap_host_function_type()

	---@type boolean, checkable|string, Environment
	local ok, tuple, env = sargs:match({
		collect_host_tuple(metalanguage.accept_handler, ExpressionArgs.new(expression_goal.check(param_type), env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		-- TODO: semantic error here crashes
		error(tuple)
		error(semantic_error.host_function_argument_collect_failed(tuple, { sargs.span }, {
			host_function_type = type_of_term,
			host_function_value = term,
		}, env))
	end
	---@cast tuple checkable

	---@type string | anchored_inferrable | checkable
	local res

	if result_info:unwrap_result_info():unwrap_result_info():is_effectful() then
		local ok, tuple_usages, tuple_term = evaluator.check(tuple, env.typechecking_context, param_type)
		if not ok then
			---@cast tuple_usages string
			return terms.tristate.failure, tuple_usages
		end
		local result_final = evaluator.apply_value(
			result_type,
			evaluator.evaluate(tuple_term, env.typechecking_context.runtime_context, env.typechecking_context),
			env.typechecking_context
		)
		local app = anchored_inferrable_term(
			start_anchor,
			unanchored_inferrable_term.typed(

				evaluator.substitute_placeholders_identity(result_final, env.typechecking_context),
				usage_array(),
				typed_term.program_invoke(
					typed_term.literal(strict_value.effect_elem(terms.lua_prog)),
					typed_term.tuple_cons(typed_term_array(term, tuple_term))
				)
			)
		)
		local bind = terms.binding.program_sequence(app, sargs.span.start)
		ok, env = env:bind_local(bind)
		if not ok then
			return terms.tristate.failure, env
		end
		ok, res = env:get("#program-sequence")
		if not ok then
			error(res)
		end
		---@cast res anchored_inferrable
	else
		res = anchored_inferrable_term(
			start_anchor,
			unanchored_inferrable_term.application(
				anchored_inferrable_term(
					start_anchor,
					unanchored_inferrable_term.typed(
						evaluator.substitute_placeholders_identity(type_of_term, env.typechecking_context),
						usage_count,
						term
					)
				),
				tuple
			)
		)
		---@cast res anchored_inferrable
	end

	if goal:is_check() then
		res = checkable_term.inferrable(res)
	end

	return terms.tristate.success, res, env
end

---@param args ExpressionArgs
---@param a ConstructedSyntax
---@param b ConstructedSyntax
---@return boolean
---@return anchored_inferrable | checkable | string | flex_value
---@return Environment?
local function expression_pairhandler(args, a, b)
	local goal, env = args:unwrap()

	-- if the expression is a list containing prefix and infix expressions,
	-- parse it into a tree of simple prefix/infix expressions with shunting yard
	local ok, syntax
	ok, syntax = shunting_yard(a, b, { n = 0 }, { n = 0 }, a.span)
	local is_operator = false
	local operator_type
	local left, operator, right
	if ok then
		---@cast syntax -string
		is_operator, operator_type, operator, left, right = syntax:match({
			metalanguage.listmatch(
				expression_prefix_handler,
				metalanguage.issymbol(metalanguage.accept_handler),
				metalanguage.any(metalanguage.accept_handler)
			),
			metalanguage.listmatch(
				expression_infix_handler,
				metalanguage.any(metalanguage.accept_handler),
				metalanguage.issymbol(metalanguage.accept_handler),
				metalanguage.any(metalanguage.accept_handler)
			),
		}, metalanguage.failure_handler, nil)
	end

	local combiner, sargs
	if is_operator and operator_type == OperatorType.Prefix then
		ok, combiner = env:get(operator .. "_")
		if not ok then
			return false, combiner
		end
		sargs = metalanguage.list(a.span, left)
	elseif is_operator and operator_type == OperatorType.Infix then
		ok, combiner = env:get("_" .. operator .. "_")
		if not ok then
			return false, combiner
		end
		sargs = metalanguage.list(a.span, left, right)
	else
		ok, combiner, env = a:match(
			{ expression(metalanguage.accept_handler, ExpressionArgs.new(expression_goal.infer, env)) },
			metalanguage.failure_handler,
			nil
		)
		if not ok then
			return false, combiner
		end
		sargs = b
	end
	---@cast combiner anchored_inferrable

	-- resolve first of the pair as an expression
	-- typecheck it
	-- check type to see how it should be combined
	-- either
	--   resolve rest of the pair as collect tuple
	--   pass it into the operative's arguments

	-- combiner was an evaluated typed value, now it isn't
	local ok, type_of_term, usage_count, term = infer(combiner, env.typechecking_context)
	if not ok then
		return false, type_of_term
	end
	local res_term1, res_term2, res_term3, res_env

	local ok
	ok, res_term1, res_env = call_operative(a.span.start, type_of_term, usage_count, term, sargs, goal, env)
	if ok:is_success() then
		return true, res_term1, res_env
	elseif ok:is_failure() then
		return false, res_term1
		--error("call_operative failed!\n" .. tostring(res_term1) .. "\n" .. type_of_term:pretty_print())
	end

	ok, res_term2, res_env = call_pi(a.span.start, type_of_term, usage_count, term, sargs, goal, env)
	if ok:is_success() then
		return true, res_term2, res_env
	elseif ok:is_failure() then
		return false, res_term2
		--error("call_pi failed!\n" .. tostring(res_term2) .. "\n" .. type_of_term:pretty_print())
	end

	ok, res_term3, res_env = call_host_func_type(a.span.start, type_of_term, usage_count, term, sargs, goal, env)
	if ok:is_success() then
		return true, res_term3, res_env
	elseif ok:is_failure() then
		return false, res_term3
		--error("call_host_func_type failed!\n" .. tostring(res_term3) .. "\n" .. type_of_term:pretty_print())
	end

	print("expressions_pairhandler speculate failed!")

	--print(combiner:pretty_print(env.typechecking_context))
	--print("infers to")
	--print(type_of_term)
	--print("in")
	--env.typechecking_context:dump_names()

	--print(type_of_term:pretty_print(env.typechecking_context))
	--print(res_term1)
	--print(res_term2)
	--print(res_term3)
	-- try uncommenting one of the error prints above
	-- you need to figure out which one is relevant for your problem
	-- after you're finished, please comment it out so that, next time, the message below can be found again
	print("debugging this is left as an exercise to the maintainer")
	return false, "unknown type for pairhandler " .. type_of_term.kind, env
end

---@param whole SyntaxSymbol
---@param remaining SyntaxSymbol
---@return SyntaxSymbol preceding_and_current
---@return SyntaxSymbol current
---@return SyntaxSymbol? remaining
local function split_dot_accessor(whole, remaining)
	if whole == nil then
		error("split_dot_accessor: whole must not be nil")
	end
	if remaining == nil then
		error("split_dot_accessor: remaining must not be nil")
	end
	local remaining_str = remaining.str
	local dot_start_pos, dot_stop_pos = remaining_str:find(".", 1, true)
	if not dot_start_pos then
		return whole, remaining, nil
	end

	local current_stop_pos, remaining_start_pos = dot_start_pos - 1, dot_stop_pos + 1
	local current_str = remaining_str:sub(1, current_stop_pos)
	local new_remaining_str = remaining_str:sub(remaining_start_pos)

	local current_start_anchor = remaining.span.start
	local current_stop_anchor = Anchor(
		current_start_anchor.internal,
		current_start_anchor.id,
		current_start_anchor.line,
		current_start_anchor.char + current_stop_pos
	)

	local current = {
		kind = "symbol",
		str = current_str,
		span = current_start_anchor:span(current_stop_anchor),
	}

	local preceding_and_current_start_anchor = whole.span.start
	local preceding_and_current_stop_anchor = current_stop_anchor
	local preceding_and_current = {
		kind = "symbol",
		str = whole.str:sub(1, preceding_and_current_stop_anchor.char - preceding_and_current_start_anchor.char),
		span = preceding_and_current_start_anchor:span(preceding_and_current_stop_anchor),
	}

	-- we can assume it is on the same line.
	local new_remaining_start_anchor = Anchor(
		current_start_anchor.internal,
		current_start_anchor.id,
		current_start_anchor.line,
		current_start_anchor.char + (remaining_start_pos - 1)
	)
	local new_remaining_stop_anchor = remaining.span.stop

	local new_remaining = {
		kind = "symbol",
		str = new_remaining_str,
		span = new_remaining_start_anchor:span(new_remaining_stop_anchor),
	}

	return preceding_and_current, current, new_remaining
end

---@param args ExpressionArgs
---@param name SyntaxSymbol
---@return boolean
---@return anchored_inferrable | checkable | string
---@return Environment?
local function expression_symbolhandler(args, name)
	local goal, env = args:unwrap()
	--print("looking up symbol", name)
	--p(env)
	--print(name, split_dot_accessor(name))
	assert(name["kind"])

	local preceding_and_current_names, current_name, remaining_names = split_dot_accessor(name, name)

	local ok, part = env:get(current_name.str)
	if not ok then
		---@cast part string
		return false, part, env
	end
	---@cast part -string
	local context_len = env.typechecking_context:len()
	while remaining_names ~= nil do
		local new_current_name, new_remaining_names
		preceding_and_current_names, new_current_name, new_remaining_names = split_dot_accessor(name, remaining_names)
		local spanned_preceding_and_current_names =
			terms.spanned_name(preceding_and_current_names.str, preceding_and_current_names.span)

		part = anchored_inferrable_term(
			preceding_and_current_names.span.start,
			unanchored_inferrable_term.record_elim(
				part,
				name_array(new_current_name.str),
				spanned_name_array(spanned_preceding_and_current_names),
				anchored_inferrable_term(
					preceding_and_current_names.span.start,
					unanchored_inferrable_term.bound_variable(context_len + 1, spanned_preceding_and_current_names)
				)
			)
		)

		remaining_names = new_remaining_names
	end
	if goal:is_check() then
		return true, U.notail(checkable_term.inferrable(part)), env
	end
	return ok, part, env
end

---@param args ExpressionArgs
---@param val SyntaxValue
---@return boolean
---@return anchored_inferrable | checkable
---@return Environment?
local function expression_valuehandler(args, val)
	local goal, env = args:unwrap()

	--TODO: proper checkable cases for literal values, requires more checkable terms
	if goal:is_check() then
		local ok, inf_term, env = expression_valuehandler(ExpressionArgs.new(expression_goal.infer, env), val)
		if not ok then
			return false, inf_term, env
		end
		---@cast inf_term -checkable
		return true, U.notail(checkable_term.inferrable(inf_term)), env
	end

	if not goal:is_infer() then
		error("expression_valuehandler NYI for " .. goal.kind)
	end

	if val.type == "f64" then
		--p(val)
		return true,
			U.notail(
				anchored_inferrable_term(
					val.span.start,
					unanchored_inferrable_term.typed(
						terms.typed_term.literal(strict_value.host_number_type),
						usage_array(),
						typed_term.literal(strict_value.host_value(val.val))
					)
				)
			),
			env
	end
	if val.type == "string" then
		return true,
			U.notail(
				anchored_inferrable_term(
					val.span.start,
					unanchored_inferrable_term.typed(
						terms.typed_term.literal(strict_value.host_string_type),
						usage_array(),
						typed_term.literal(strict_value.host_value(val.val))
					)
				)
			),
			env
	end
	p("valuehandler error", val)
	error("unknown value type " .. val.type)
end

expression = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param args ExpressionArgs
	---@return boolean
	---@return anchored_inferrable|checkable|string
	---@return Environment?
	function(syntax, args)
		-- p(syntax)
		return syntax:match({
			metalanguage.ispair(expression_pairhandler),
			metalanguage.issymbol(expression_symbolhandler),
			metalanguage.isvalue(expression_valuehandler),
		}, metalanguage.failure_handler, args)
	end,
	"expressions"
)

-- local constexpr =
--   metalanguage.reducer(
--     function(syntax, environment)
--       local ok, val =
--         syntax:match({expressions(metalanguage.accept_handler, environment)}, metalanguage.failure_handler, nil)
--       if not ok then return false, val end
--       return val:asconstant()
--     enfoundendd
--   )

-- operate_behavior[types.primop_kind] = function(self, ops, env)
--   -- print("evaluating operative")
--   -- p(self)
--   -- p(ops)
--   -- p(env)
--   return self.val(ops, env)
-- end

---@class OperativeError
---@field cause any
---@field span Span
---@field operative_name string
local OperativeError = {}
local external_error_mt = {
	__tostring = function(self)
		local message = "Lua error occurred inside host operative "
			.. self.operative_name
			.. " "
			.. (self.span and tostring(self.span) or " at unknown position")
			.. ":\n"
			.. tostring(self.cause)
		return message
	end,
	__index = OperativeError,
}

---@param cause any
---@param span Span
---@param operative_name string
---@return OperativeError
function OperativeError.new(cause, span, operative_name)
	return setmetatable({
		span = span,
		cause = cause,
		operative_name = operative_name,
	}, external_error_mt)
end

---@param fn lua_operative
---@param name string
---@return anchored_inferrable
local function host_operative(fn, name)
	local short_src = "<no debug info>"
	local linedef = 0
	if debug then
		local debuginfo = debug.getinfo(fn)
		short_src = debuginfo.short_src
		linedef = debuginfo.linedefined
	end
	local debugstring = (name or error("name not passed to host_operative")) .. " " .. short_src .. ":" .. linedef
	local aborting_fn = function(syn, env, userdata, goal)
		if not env or not env.exit_block then
			error("env passed to host_operative " .. debugstring .. " isn't an env or is nil", env)
		end
		-- userdata isn't passed in as it's always empty for host operatives
		local ok, res, env = fn(syn, env, goal)
		if not ok then
			error(OperativeError.new(res, syn.span, debugstring))
		end
		if
			(goal:is_infer() and anchored_inferrable_term.value_check(res))
			or (goal:is_check() and checkable_term.value_check(res))
		then
			-- nothing to do, all is well
		elseif goal:is_check() and anchored_inferrable_term.value_check(res) then
			-- workaround host operatives that ignore goal and assume inferrable
			---@cast res anchored_inferrable
			res = checkable_term.inferrable(res)
		else
			error("mismatch in goal and returned term\ngoal: " .. tostring(goal) .. "\nres: " .. tostring(res))
		end
		if not env or not env.exit_block then
			print(
				"env returned from fn passed to alicorn-expressions.host_operative isn't an env or is nil",
				env,
				" in ",
				short_src,
				linedef
			)
			error("invalid env from host_operative fn " .. debugstring)
		end
		return res, env
	end

	-- what we're going for:
	-- (s : syntax, e : environment, u : wrapped_typed_term(userdata), g : goal) -> (goal_to_term(g), environment)
	--   goal one of inferable, mechanism, checkable

	local args_dbg = spanned_name("#args", format.span_here())
	local arg_unpack_dbg = spanned_name_array(
		spanned_name("#syn", format.span_here()),
		spanned_name("#env", format.span_here()),
		spanned_name("#ud", format.span_here()),
		spanned_name("#goal", format.span_here())
	)
	local result_unpack_dbg =
		spanned_name_array(spanned_name("#res-term", format.span_here()), spanned_name("#res-env", format.span_here()))

	-- 1: wrap fn as a typed host_value
	-- this way it can take a host tuple and return a host tuple
	local typed_host_fn = typed_term.literal(strict_value.host_value(aborting_fn))
	-- 2: wrap it to convert a normal tuple argument to a host tuple
	-- and a host tuple result to a normal tuple
	-- this way it can take a normal tuple and return a normal tuple
	local nparams = 4
	local tuple_conv_elements = typed_term_array(
		typed_term.bound_variable(3, result_unpack_dbg[1]),
		typed_term.bound_variable(4, result_unpack_dbg[2])
	)
	local host_tuple_conv_elements = typed_term_array()
	for i = 1, nparams do
		-- + 2 because variable 2 is the argument tuple
		-- all variables that follow are the destructured tuple
		local var = typed_term.bound_variable(i + 2, arg_unpack_dbg[i])
		host_tuple_conv_elements:append(var)
	end
	local tuple_conv = typed_term.tuple_cons(tuple_conv_elements)
	local host_tuple_conv = typed_term.host_tuple_cons(host_tuple_conv_elements)
	local param_names = name_array("#syntax", "#env", "#userdata", "#goal")
	local tuple_to_host_tuple = typed_term.tuple_elim(
		param_names,
		arg_unpack_dbg,
		typed_term.bound_variable(2, args_dbg),
		nparams,
		host_tuple_conv
	)
	local tuple_to_host_tuple_fn = typed_term.application(typed_host_fn, tuple_to_host_tuple)
	local result_names = name_array("#term", "#env")
	local tuple_to_tuple_fn =
		typed_term.tuple_elim(result_names, result_unpack_dbg, tuple_to_host_tuple_fn, 2, tuple_conv)
	-- 3: wrap it in a closure with an empty capture, not a typed lambda
	-- this ensures variable 1 is the argument tuple
	local value_fn = strict_value.closure(
		"#" .. name .. "_PARAM",
		tuple_to_tuple_fn,
		empty_tuple,
		spanned_name("#capture", format.span_here()),
		args_dbg
	)

	local userdata_type = strict_value.tuple_type(terms.empty:unwrap_strict())
	return U.notail(
		anchored_inferrable_term(
			format.anchor_here(2),
			unanchored_inferrable_term.typed(

				terms.typed_term.literal(strict_value.operative_type(value_fn, userdata_type)),
				array(gen.builtin_integer)(),
				typed_term.operative_cons(typed_term.tuple_cons(typed_term_array()))
			)
		)
	)
end

---@param args ExpressionArgs
---@param a ConstructedSyntax
---@param b ConstructedSyntax
---@return boolean
---@return string|boolean
---@return checkable?
---@return ConstructedSyntax?
---@return Environment?
local function collect_tuple_pair_handler(args, a, b)
	local goal, env = args:unwrap()
	local ok, val
	ok, val, env = a:match(
		{ expression(metalanguage.accept_handler, ExpressionArgs.new(goal, env)) },
		metalanguage.failure_handler,
		nil
	)
	if not ok then
		return false, val
	end
	return true, true, val, b, env
end

---@param args ExpressionArgs
---@return boolean
---@return boolean
---@return nil
---@return nil
---@return Environment
local function collect_tuple_nil_handler(args)
	local goal, env = args:unwrap()
	return true, false, nil, nil, env
end

collect_tuple = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param args ExpressionArgs
	---@return boolean
	---@return string|anchored_inferrable|checkable
	---@return Environment?
	function(syntax, args)
		local goal, env = args:unwrap()
		local goal_type, collected_terms
		local desc = terms.empty

		local start_anchor = syntax.span.start

		if goal:is_check() then
			collected_terms = array(checkable_term)()
			goal_type = goal:unwrap_check()
		else
			collected_terms = anchored_inferrable_term_array()
		end

		local collected_info = spanned_name_array()
		local ok, continue, next_term = true, true, nil
		local i = 0
		while ok and continue do
			i = i + 1
			if goal_type then
				local next_elem_type_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
				local next_elem_type = next_elem_type_mv:as_flex()
				ok, continue, next_term, syntax, env = syntax:match({
					metalanguage.ispair(collect_tuple_pair_handler),
					metalanguage.isnil(collect_tuple_nil_handler),
				}, metalanguage.failure_handler, ExpressionArgs.new(expression_goal.check(next_elem_type), env))
				if ok and continue then
					collected_terms:append(next_term)
					local ok, typed_usages, next_typed =
						evaluator.check(next_term, env.typechecking_context, next_elem_type)
					if not ok then
						return false, typed_usages
					end
					local next_val = evaluator.evaluate(
						next_typed,
						env.typechecking_context.runtime_context,
						env.typechecking_context
					)
					local info = spanned_name("#collect-tuple-param", syntax.span)
					desc = terms.cons(
						desc,
						evaluator.substitute_into_closure(
							flex_value.singleton(next_elem_type, next_val),
							env.typechecking_context.runtime_context,
							syntax.span,
							info,
							env.typechecking_context
						)
					)
					collected_info:append(info)
				end
				if not ok and type(continue) == "string" then
					continue = continue
						.. " (should have "
						.. ", found "
						.. tostring(collected_terms:len())
						.. " so far)"
				end
			else
				ok, continue, next_term, syntax, env = syntax:match({
					metalanguage.ispair(collect_tuple_pair_handler),
					metalanguage.isnil(collect_tuple_nil_handler),
				}, metalanguage.failure_handler, ExpressionArgs.new(goal, env))
				if ok and continue then
					collected_terms:append(next_term)
				end
			end
		end
		if not ok then
			return false, continue
		end

		if goal:is_infer() then
			return true,
				U.notail(
					anchored_inferrable_term(
						start_anchor,
						unanchored_inferrable_term.tuple_cons(collected_terms, collected_info)
					)
				),
				env
		elseif goal:is_check() then
			local ok, err = evaluator.typechecker_state:flow(
				flex_value.tuple_type(desc),
				env.typechecking_context,
				goal_type,
				env.typechecking_context,
				terms.constraintcause.primitive("tuple type in collect_tuple", format.anchor_here())
			)

			if not ok then
				return false, err
			end

			--[[U.tag(
				"flow",
				{
					val = flex_value.tuple_type(desc):pretty_preprint(env.typechecking_context),
					use = goal_type:pretty_preprint(env.typechecking_context),
				},
				evaluator.typechecker_state.flow,
				evaluator.typechecker_state,
				flex_value.tuple_type(desc),
				env.typechecking_context,
				goal_type,
				env.typechecking_context,
				terms.constraintcause.primitive("tuple type in collect_tuple", format.anchor_here())
			)]]
			return true, U.notail(checkable_term.tuple_cons(collected_terms, collected_info)), env
		else
			error("NYI: collect_tuple goal case " .. goal.kind)
		end
	end,
	"collect_tuple"
)

collect_host_tuple = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param args ExpressionArgs
	---@return boolean
	---@return string|anchored_inferrable|checkable
	---@return Environment?
	function(syntax, args)
		local goal, env = args:unwrap()
		local goal_type, collected_terms
		local desc = terms.empty
		local collected_debug = spanned_name_array()

		if goal:is_check() then
			collected_terms = array(checkable_term)()
			goal_type = goal:unwrap_check()
		else
			collected_terms = anchored_inferrable_term_array()
		end

		local ok, continue, next_term = true, true, nil
		local i = 0
		while ok and continue do
			i = i + 1
			if goal_type then
				local next_elem_type_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
				local next_elem_type = next_elem_type_mv:as_flex()
				ok, continue, next_term, syntax, env = syntax:match({
					metalanguage.ispair(collect_tuple_pair_handler),
					metalanguage.isnil(collect_tuple_nil_handler),
				}, metalanguage.failure_handler, ExpressionArgs.new(expression_goal.check(next_elem_type), env))
				if ok and continue then
					collected_terms:append(next_term)
					collected_debug:append(spanned_name("#collected_term", syntax.span))
					local ok, typed_usages, next_typed =
						evaluator.check(next_term, env.typechecking_context, next_elem_type)
					if not ok then
						return false, typed_usages
					end
					local next_val = evaluator.evaluate(
						next_typed,
						env.typechecking_context.runtime_context,
						env.typechecking_context
					)
					desc = terms.cons(
						desc,
						evaluator.substitute_into_closure(
							flex_value.singleton(next_elem_type, next_val),
							env.typechecking_context.runtime_context,
							syntax.span,
							spanned_name("#collect-host-tuple-param", syntax.span),
							env.typechecking_context
						)
					)
				end
				if not ok and type(continue) == "string" then
					continue = continue
						.. " (should have "
						.. ", found "
						.. tostring(collected_terms:len())
						.. " so far)"
				end
			else
				ok, continue, next_term, syntax, env = syntax:match({
					metalanguage.ispair(collect_tuple_pair_handler),
					metalanguage.isnil(collect_tuple_nil_handler),
				}, metalanguage.failure_handler, ExpressionArgs.new(goal, env))
				if ok and continue then
					collected_terms:append(next_term)
					collected_debug:append(spanned_name("#collected_term", syntax.span))
				end
			end
		end
		if not ok then
			return false, continue
		end

		if goal:is_infer() then
			return true,
				U.notail(
					anchored_inferrable_term(
						syntax.span.start,
						unanchored_inferrable_term.host_tuple_cons(collected_terms, collected_debug)
					)
				),
				env
		elseif goal:is_check() then
			local ok, err = evaluator.typechecker_state:flow(
				flex_value.host_tuple_type(desc),
				env.typechecking_context,
				goal_type,
				env.typechecking_context,
				terms.constraintcause.primitive("host tuple type in collect_host_tuple", format.anchor_here())
			)
			if not ok then
				return false, err
			end
			return true, U.notail(checkable_term.host_tuple_cons(collected_terms, collected_debug)), env
		else
			error("NYI: collect_host_tuple goal case " .. goal.kind)
		end
	end,
	"collect_host_tuple"
)

local expressions_args = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param args ExpressionArgs
	---@return boolean
	---@return anchored_inferrable[]|checkable[]|string
	---@return Environment?
	function(syntax, args)
		local goal, env = args:unwrap()
		local vals = {}
		local ok, continue = true, true
		while ok and continue do
			ok, continue, vals[#vals + 1], syntax, env = syntax:match({
				metalanguage.ispair(collect_tuple_pair_handler),
				metalanguage.isnil(collect_tuple_nil_handler),
			}, metalanguage.failure_handler, ExpressionArgs.new(goal, env))
		end
		if not ok then
			return false, continue
		end
		return true, vals, env
	end,
	"expressions_args"
)

local block = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param args ExpressionArgs
	---@return boolean
	---@return anchored_inferrable|checkable|string
	---@return Environment?
	function(syntax, args)
		local goal, env = args:unwrap()
		if not goal:is_infer() then
			error("NYI non-infer cases for block")
		end

		local lastval = anchored_inferrable_term(
			syntax.span.start,
			unanchored_inferrable_term.tuple_cons(anchored_inferrable_term_array(), spanned_name_array())
		)

		local newval
		local ok, continue = true, true
		while ok and continue do
			ok, continue, newval, syntax, env = syntax:match({
				metalanguage.ispair(collect_tuple_pair_handler),
				metalanguage.isnil(collect_tuple_nil_handler),
			}, metalanguage.failure_handler, ExpressionArgs.new(goal, env))
			if ok and continue then
				lastval = newval
			end
		end
		if not ok then
			return false, continue
		end
		return true, lastval, env
	end,
	"block"
)

---@param args ExpressionArgs
---@param a ConstructedSyntax
---@param b ConstructedSyntax
---@return boolean
---@return string|boolean
---@return ConstructedSyntax?
---@return checkable?
---@return ConstructedSyntax?
---@return Environment?
local function top_level_block_pair_handler(args, a, b)
	local goal, env = args:unwrap()
	local ok, val
	ok, val, env = a:match(
		{ expression(metalanguage.accept_handler, ExpressionArgs.new(goal, env)) },
		metalanguage.failure_handler,
		nil
	)
	if not ok then
		return false, val
	end
	return true, true, a, val, b, env
end

---@param args ExpressionArgs
---@return boolean
---@return boolean
---@return nil
---@return nil
---@return nil
---@return Environment
local function top_level_block_nil_handler(args)
	local goal, env = args:unwrap()
	return true, false, nil, nil, nil, env
end

local top_level_block = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param args TopLevelBlockArgs
	---@return boolean
	---@return anchored_inferrable|checkable|string
	---@return Environment?
	function(syntax, args)
		local goal, env = args.exprargs:unwrap()
		if not goal:is_infer() then
			error("NYI non-infer cases for block")
		end
		local lastval = anchored_inferrable_term(
			syntax.span.start,
			unanchored_inferrable_term.tuple_cons(anchored_inferrable_term_array(), spanned_name_array())
		)
		local newval
		local ok, continue = true, true

		--slightly hacky length measurement, but oh well
		local length, tail = 0, syntax
		while ok and continue do
			ok, continue, tail = tail:match({
				metalanguage.ispair(function(ud, a, b)
					return true, true, b
				end),
				metalanguage.isnil(function(ud)
					return true, false
				end),
			}, metalanguage.failure_handler, nil)
			if not ok then
				return false, continue
			end
			length = length + 1
		end
		continue = true
		io.write(
			"processing "
				.. tostring(args.name)
				.. " --- 0 / "
				.. tostring(length)
				.. " @ "
				.. tostring(tail and tail.span or (syntax and syntax.span) or "")
				.. ""
		)
		local progress = 0
		while ok and continue do
			local aval
			ok, continue, aval, newval, syntax, env = syntax:match({
				metalanguage.ispair(top_level_block_pair_handler),
				metalanguage.isnil(top_level_block_nil_handler),
			}, metalanguage.failure_handler, ExpressionArgs.new(goal, env))
			if ok and continue then
				lastval = newval
			end
			progress = progress + 1
			local line_setup_sequence = ""
			if U.file_is_terminal() then
				line_setup_sequence = "\x1bM"
			end
			io.write(
				line_setup_sequence
					.. "\rprocessing "
					.. tostring(args.name)
					.. " --- "
					.. tostring(progress)
					.. " / "
					.. tostring(length)
					.. " @ "
					.. tostring(aval and aval.span or (syntax and syntax.span) or "")
					.. ""
			)
			io.flush()
		end
		io.write("\n")
		if not ok then
			io.write("Failed!\n")
			return false, continue
		end
		io.write("Finished!\n")
		return true, lastval, env
	end,
	"block"
)

-- example usage of primitive_applicative
-- add(a, b) = a + b ->
-- local prim_num = terms.strict_value.prim_number_type
-- primitive_applicative(function(a, b) return a + b end, {prim_num, prim_num}, {prim_num}),

---@param elems strict_value[]
---@return strict_value
local function build_host_type_tuple(elems)
	local result = terms.empty:unwrap_strict()

	for _, v in ipairs(elems) do
		result = strict_value.enum_value(
			terms.DescCons.cons,
			strict_value.tuple_value(strict_value_array(result, const_combinator(v)))
		)
	end

	return U.notail(terms.strict_value.host_tuple_type(result))
end

---@param fn function
---@param params strict_value[]
---@param results strict_value[]
---@return anchored_inferrable
local function host_applicative(fn, params, results)
	local literal_host_fn = terms.typed_term.literal(terms.strict_value.host_value(fn))
	local host_fn_type = terms.strict_value.host_function_type(
		build_host_type_tuple(params),
		build_host_type_tuple(results),
		result_info_pure
	)
	return U.notail(
		anchored_inferrable_term(
			format.anchor_here(2),
			unanchored_inferrable_term.typed(terms.typed_term.literal(host_fn_type), usage_array(), literal_host_fn)
		)
	)
end

---@param syntax ConstructedSyntax
---@param environment Environment
---@return ...
local function eval(syntax, environment)
	return syntax:match(
		{ expression(metalanguage.accept_handler, ExpressionArgs.new(expression_goal.infer, environment)) },
		metalanguage.failure_handler,
		nil
	)
end

---@param syntax ConstructedSyntax
---@param environment Environment
---@return ...
local function eval_block(syntax, environment)
	return syntax:match(
		{ block(metalanguage.accept_handler, ExpressionArgs.new(expression_goal.infer, environment)) },
		metalanguage.failure_handler,
		nil
	)
end

---Convenience wrapper inferred_expression(handler, env) -> expression(handler, expression_args(expression_goal.infer, env))
---@generic T
---@param handler fun(u: T, ...):...
---@param env Environment
---@return any
local function inferred_expression(handler, env)
	if handler == nil then
		error("no handler")
	end
	if env == nil or env.get == nil then
		error("no env")
	end
	return U.notail(expression(handler, ExpressionArgs.new(expression_goal.infer, env)))
end

local alicorn_expressions = {
	expression = expression,
	inferred_expression = inferred_expression,
	-- constexpr = constexpr
	block = block,
	top_level_block = top_level_block,
	ExpressionArgs = ExpressionArgs,
	host_operative = host_operative,
	host_applicative = host_applicative,
	--define_operate = define_operate,
	collect_tuple = collect_tuple,
	expressions_args = expressions_args,
	eval = eval,
	eval_block = eval_block,
}
local internals_interface = require "internals-interface"
internals_interface.alicorn_expressions = alicorn_expressions
return alicorn_expressions
