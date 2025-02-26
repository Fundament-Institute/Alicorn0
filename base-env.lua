-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local environment = require "environment"
local trie = require "lazy-prefix-tree"
local metalanguage = require "metalanguage"
local utils = require "reducer-utils"
local exprs = require "alicorn-expressions"
local terms = require "terms"
local gen = require "terms-generators"
local evaluator = require "evaluator"
local U = require "alicorn-utils"
local format = require "format"

local strict_value, strict_value_array = terms.strict_value, terms.strict_value_array
local stuck_value = terms.stuck_value
local flex_value, flex_value_array = terms.flex_value, terms.flex_value_array
local anchored_inferrable_term, anchored_inferrable_term_array =
	terms.anchored_inferrable_term, terms.anchored_inferrable_term_array
local unanchored_inferrable_term = terms.unanchored_inferrable_term
local typed_term, typed_term_array = terms.typed_term, terms.typed_term_array
local spanned_name, spanned_name_array = terms.spanned_name, terms.spanned_name_array

local param_info_explicit = strict_value.param_info(strict_value.visibility(terms.visibility.explicit))
local result_info_pure = strict_value.result_info(terms.result_info(terms.purity.pure))
local result_info_effectful = strict_value.result_info(terms.result_info(terms.purity.effectful))

local usage_array = gen.declare_array(gen.builtin_integer)
local name_array = gen.declare_array(gen.builtin_string)
local empty_tuple = terms.strict_value.tuple_value(strict_value_array())

local gen_base_operator = evaluator.gen_base_operator

---@param val strict_value
---@param typ strict_value
---@return anchored_inferrable
local function lit_term(val, typ)
	return U.notail(
		anchored_inferrable_term(
			format.anchor_here(2),
			unanchored_inferrable_term.typed(typed_term.literal(typ), usage_array(), typed_term.literal(val))
		)
	)
end

--- lua_operative is dependently typed and should produce inferrable vs checkable depending on the goal, and an error as the second return if it failed
--- | unknown in the second return insufficiently constrains the non-error cases to be inferrable or checkable terms
--- this can be fixed in the future if we swap to returning a Result type that can express the success/error constraint separately
---@alias lua_operative fun(syntax : ConstructedSyntax, env : Environment, goal : expression_goal) : boolean, anchored_inferrable | checkable | string, Environment?

---handle a let binding
---@type lua_operative
local function let_impl(syntax, env)
	local ok, name, tail = syntax:match({
		metalanguage.listtail(
			metalanguage.accept_handler,
			metalanguage.oneof(
				metalanguage.accept_handler,
				metalanguage.issymbol(metalanguage.accept_handler),
				metalanguage.list_many(metalanguage.accept_handler, metalanguage.issymbol(metalanguage.accept_handler))
			),
			metalanguage.symbol_exact(metalanguage.accept_handler, "=")
		),
	}, metalanguage.failure_handler, nil)

	if not ok then
		return false, name
	end

	local expr
	ok, expr = tail:match({
		metalanguage.listmatch(metalanguage.accept_handler, metalanguage.any(metalanguage.accept_handler)),
	}, metalanguage.failure_handler)
	if not ok then
		expr = tail
	end

	local bind
	ok, bind = expr:match({
		exprs.inferred_expression(utils.accept_with_env, env),
	}, metalanguage.failure_handler, nil)

	if not ok then
		return false, bind
	end
	local expr, env = utils.unpack_val_env(bind)

	if not env or not env.get then
		p(env)
		error("env in let_impl isn't an env")
	end

	if not name["kind"] then
		--print("binding destructuring with let")
		local debugs = spanned_name_array()
		for _, v in ipairs(name) do
			debugs:append(spanned_name(v.str, v.span))
			if v.kind == nil then
				error("v.kind is nil")
			end
		end

		ok, env = env:bind_local(terms.binding.tuple_elim(
			debugs:map(name_array, function(d)
				return d.name
			end),
			debugs,
			expr
		))
		if not ok then
			return false, env
		end
	else
		if name["kind"] == nil then
			error("name['kind'] is nil")
		end
		ok, env = env:bind_local(terms.binding.let(name.str, spanned_name(name.str, name.span), expr))
		if not ok then
			return false, env
		end
	end

	return true,
		U.notail(
			anchored_inferrable_term(
				syntax.span.start,
				unanchored_inferrable_term.typed(
					typed_term.literal(terms.unit_type),
					usage_array(),
					typed_term.literal(terms.unit_val)
				)
			)
		),
		env
end

---@type lua_operative
local function mk_impl(syntax, env)
	local ok, bun = syntax:match({
		metalanguage.listmatch(
			metalanguage.accept_handler,
			metalanguage.listtail(utils.accept_bundled, metalanguage.issymbol(metalanguage.accept_handler))
		),
		metalanguage.listtail(utils.accept_bundled, metalanguage.issymbol(metalanguage.accept_handler)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, bun
	end
	local name, tail = utils.unpack_bundle(bun)
	local tuple
	ok, tuple, env = tail:match({
		exprs.collect_tuple(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, tuple
	end
	return ok,
		U.notail(anchored_inferrable_term(syntax.span.start, unanchored_inferrable_term.enum_cons(name.str, tuple))),
		env
end

---@type Matcher
local switch_case_header_matcher = metalanguage.listtail(
	metalanguage.accept_handler,
	metalanguage.oneof(
		metalanguage.accept_handler,
		metalanguage.issymbol(utils.accept_bundled),
		metalanguage.list_many(metalanguage.accept_handler, metalanguage.issymbol(metalanguage.accept_handler))
	),
	metalanguage.symbol_exact(metalanguage.accept_handler, "->")
)

---@param syntax ConstructedSyntax
---@param env Environment
---@return boolean ok
---@return (any | Environment) tag
---@return any term
---@return Environment env
local switch_case = metalanguage.reducer(function(syntax, env)
	local ok, tag, tail = syntax:match({ switch_case_header_matcher }, metalanguage.failure_handler, nil)
	if not ok then
		return ok, tag
	end

	local tag_length = #tag
	---@type spanned_name[]
	local names = {}
	for i = 2, tag_length do
		local name = tag[i]
		names[i - 1] = spanned_name(name.str, name.span)
	end
	names = spanned_name_array:new(names)
	tag = tag[1]

	if not tag then
		return false, "missing case tag"
	end
	local singleton_contents
	ok, singleton_contents = tail:match({
		metalanguage.listmatch(metalanguage.accept_handler, metalanguage.any(metalanguage.accept_handler)),
	}, metalanguage.failure_handler, nil)
	if ok then
		tail = singleton_contents
	end
	local case_info = spanned_name(tag.str, tag.span)
	--TODO rewrite this to use an environment-splitting operation
	env = environment.new_env(env, {
		typechecking_context = env.typechecking_context:append(
			tag.str,
			evaluator.typechecker_state:metavariable(env.typechecking_context):as_flex(),
			nil,
			case_info
		),
	})
	local shadowed, term
	shadowed, env = env:enter_block(terms.block_purity.inherit)
	ok, env = env:bind_local(
		terms.binding.tuple_elim(
			names:map(name_array, function(name)
				local name_string, _ = name:unwrap_spanned_name()
				return name_string
			end),
			names,

			anchored_inferrable_term(
				syntax.span.start,
				unanchored_inferrable_term.bound_variable(env.typechecking_context:len(), case_info)
			)
		)
	)
	if not ok then
		return false, env
	end
	ok, term, env = tail:match({
		exprs.inferred_expression(metalanguage.accept_handler, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, term
	end
	env, term = env:exit_block(term, shadowed)
	return ok, tag, term, env
end, "switch_case")

---@type lua_operative
local function switch_impl(syntax, env)
	local ok, subj
	ok, subj, syntax = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, exprs.inferred_expression(utils.accept_bundled, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, subj
	end
	subj, env = table.unpack(subj)
	local variants = gen.declare_map(gen.builtin_string, anchored_inferrable_term)()
	local variant_debug = gen.declare_map(gen.builtin_string, spanned_name)()
	while not syntax:match({ metalanguage.isnil(metalanguage.accept_handler) }, metalanguage.failure_handler, nil) do
		local tag, term
		ok, tag, syntax = syntax:match({
			metalanguage.listtail(metalanguage.accept_handler, switch_case(utils.accept_bundled, env)),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, tag
		end
		--TODO rewrite this to collect the branch envs and join them back together:
		tag, term = table.unpack(tag)
		variants:set(tag.str, term)
		variant_debug:set(tag.str, spanned_name(tag.str, tag.span))
	end
	return true,
		U.notail(
			anchored_inferrable_term(
				syntax.span.start,
				unanchored_inferrable_term.enum_case(subj, variants, variant_debug)
			)
		),
		env
end

---@param _ any
---@param symbol SyntaxSymbol
---@param exprenv { val:anchored_inferrable, env:Environment }
---@return boolean
---@return { name:string, expr:anchored_inferrable }
---@return Environment
local function record_threaded_element_acceptor(_, symbol, exprenv)
	local expr, env = utils.unpack_val_env(exprenv)
	return true, { name = symbol.str, expr = expr }, env
end

---@param env Environment
---@return Matcher
local function record_threaded_element(env)
	return U.notail(
		metalanguage.listmatch(
			record_threaded_element_acceptor,
			metalanguage.issymbol(metalanguage.accept_handler),
			metalanguage.symbol_exact(metalanguage.accept_handler, "="),
			exprs.inferred_expression(utils.accept_with_env, env)
		)
	)
end

---@type lua_operative
local function record_of_impl(syntax, env)
	local ok, defs, env = syntax:match({
		metalanguage.list_many_fold(metalanguage.accept_handler, record_threaded_element, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, defs
	end
	local map = gen.declare_map(gen.builtin_string, anchored_inferrable_term)()
	for _, v in ipairs(defs) do
		map:set(v.name, v.expr)
	end
	return true, U.notail(anchored_inferrable_term(syntax.span.start, unanchored_inferrable_term.record_cons(map))), env
end

---@type lua_operative
local function intrinsic_impl(syntax, env)
	local start_anchor = syntax.span.start

	local ok, str_env, syntax = syntax:match({
		metalanguage.listtail(
			metalanguage.accept_handler,
			exprs.expression(
				utils.accept_with_env,
				exprs.ExpressionArgs.new(
					terms.expression_goal.check(flex_value.strict(strict_value.host_string_type)),
					env
				)
			),
			metalanguage.symbol_exact(metalanguage.accept_handler, ":")
		),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, str_env
	end
	local str, env = utils.unpack_val_env(str_env)
	if not env then
		error "env nil in base-env.intrinsic"
	end
	local ok, type_env = syntax:match({
		metalanguage.listmatch(metalanguage.accept_handler, exprs.inferred_expression(utils.accept_with_env, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, type_env
	end
	local type, env = utils.unpack_val_env(type_env)
	if not env then
		error "env nil in base-env.intrinsic"
	end
	return true,
		U.notail(
			anchored_inferrable_term(
				start_anchor,
				unanchored_inferrable_term.host_intrinsic(
					str,
					type --[[terms.checkable_term.inferrable(type)]],
					start_anchor
				)
			)
		),
		env
end

---make a checkable term of a specific literal purity
---@param purity purity
---@return checkable
local function make_literal_purity(purity)
	return U.notail(
		terms.checkable_term.inferrable(
			anchored_inferrable_term(
				format.anchor_here(2),
				unanchored_inferrable_term.typed(
					typed_term.literal(terms.host_purity_type),
					usage_array(),
					typed_term.literal(strict_value.host_value(purity))
				)
			)
		)
	)
end
local literal_purity_pure = make_literal_purity(terms.purity.pure)
local literal_purity_effectful = make_literal_purity(terms.purity.effectful)

local pure_ascribed_name = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return spanned_name
	---@return anchored_inferrable?
	---@return Environment?
	function(syntax, env)
		local ok, name, tail = syntax:match({
			metalanguage.issymbol(metalanguage.accept_handler),
			metalanguage.listtail(
				metalanguage.accept_handler,
				metalanguage.issymbol(metalanguage.accept_handler),
				metalanguage.symbol_exact(metalanguage.accept_handler, ":")
			),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, name
		end
		local type
		if tail then
			local ok, type_env = tail:match({
				metalanguage.listmatch(
					metalanguage.accept_handler,
					exprs.inferred_expression(utils.accept_with_env, env)
				),
			}, metalanguage.failure_handler, nil)
			if not ok then
				return ok, type_env
			end
			type, env = utils.unpack_val_env(type_env)
		else
			local type_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
			type = anchored_inferrable_term(
				syntax.span.start,

				unanchored_inferrable_term.typed(
					typed_term.literal(strict_value.star(evaluator.OMEGA, 1)),
					usage_array(),
					typed_term.metavariable(type_mv)
				)
			)
		end
		return true, spanned_name(name.str, name.span), type, env
	end,
	"pure_ascribed_name"
)

---@param build_names_binding (fun(names: spanned_name[], prev: anchored_inferrable): (names_binding: binding))
---@return Reducer ascribed_name
local function ascribed_name(build_names_binding)
	return metalanguage.reducer(
		---@param syntax ConstructedSyntax
		---@param env Environment
		---@param prev anchored_inferrable
		---@param names spanned_name[]
		---@return boolean
		---@return spanned_name
		---@return anchored_inferrable?
		---@return Environment?
		function(syntax, env, prev, names)
			-- print("ascribed_name trying")
			-- p(syntax)
			-- print(prev:pretty_print())
			-- print("is env an environment? (start of ascribed name)")
			-- print(env.get)
			-- print(env.enter_block)
			local shadowed
			shadowed, env = env:enter_block(terms.block_purity.pure)
			local prev_name = "#prev - " .. tostring(syntax.span)
			local ok
			ok, env = env:bind_local(
				terms.binding.annotated_lambda(
					prev_name,
					prev,
					syntax.span.start,
					terms.visibility.explicit,
					literal_purity_pure
				)
			)
			if not ok then
				return false, env
			end
			local ok, prev_binding = env:get(prev_name)
			if not ok then
				error "#prev should always be bound, was just added"
			end
			---@cast prev_binding -string
			ok, env = env:bind_local(build_names_binding(names, prev_binding))
			if not ok then
				return false, env
			end
			local ok, name, val, env = syntax:match(
				{ pure_ascribed_name(metalanguage.accept_handler, env) },
				metalanguage.failure_handler,
				nil
			)
			if not ok then
				return ok, name
			end
			---@cast env Environment
			local env, val, purity = env:exit_block(val, shadowed)
			-- print("is env an environment? (end of ascribed name)")
			-- print(env.get)
			-- print(env.enter_block)
			return true, name, val, env
		end,
		"ascribed_name"
	)
end

local curry_segment = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return Environment|string
	function(syntax, env)
		--print("start env: " .. tostring(env))

		local ok, env = syntax:match({
			metalanguage.list_many_fold(function(_, vals, thread)
				return true, thread.env
			end, function(thread)
				--print("type_env: " .. tostring(thread.env))
				return U.notail(pure_ascribed_name(function(_, name, type_val, type_env)
					local ok
					local str, span = name:unwrap_spanned_name()
					ok, type_env = type_env:bind_local(
						terms.binding.annotated_lambda(
							str,
							type_val,
							span.start,
							terms.visibility.implicit,
							literal_purity_pure
						)
					)
					if not ok then
						return false, type_env
					end
					local newthread = {
						env = type_env,
					}
					return true, { name = name, type = type_val }, newthread
				end, thread.env))
			end, {
				env = env,
			}),
		}, metalanguage.failure_handler, nil)

		if not ok then
			return ok, env
		end

		--print("env return: " .. tostring(env))

		return true, env
	end,
	"curry_segment"
)

---@type lua_operative
local function lambda_curry_impl(syntax, env)
	local shadow, env = env:enter_block(terms.block_purity.pure)

	local ok, env, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, curry_segment(metalanguage.accept_handler, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, env
	end

	local ok, expr, env = tail:match(
		{ exprs.block(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, env)) },
		metalanguage.failure_handler,
		nil
	)
	if not ok then
		return ok, expr
	end
	local resenv, term, purity = env:exit_block(expr, shadow)
	return true, term, resenv
end

local record_ascribed_name = ascribed_name(function(names, prev)
	return terms.binding.record_elim(
		names,
		names:map(name_array, function(n)
			return n.name
		end),
		prev
	)
end)

local record_desc_of_ascribed_names = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: spanned_name[], args: anchored_inferrable, env: Environment}|string
	function(syntax, env)
		local names = spanned_name_array()

		local ok, acc = syntax:match({
			metalanguage.list_many_fold(function(_userdata, vals, acc)
				return true, acc
			end, function(acc, span)
				---@type unanchored_inferrable
				local acc_args = acc.args
				local new_desc_cons = acc_args:unwrap_record_desc_cons():copy()

				return record_ascribed_name(function(_userdata, name, type_val, type_env)
					local names = acc.names:copy()
					local str, _ = name:unwrap_spanned_name()
					new_desc_cons:set(str, type_val)
					names:append(name)
					local new_acc = {
						names = names,
						args = terms.unanchored_inferrable_term.record_desc_cons(new_desc_cons),
						env = type_env,
					}
					return true, { name = name, type = type_val }, new_acc
				end, acc.env, anchored_inferrable_term(syntax.span.start, acc.args), acc.names)
			end, {
				names = names,
				args = terms.unanchored_inferrable_term.record_desc_cons(
					gen.declare_map(gen.builtin_string, anchored_inferrable_term)()
				),
				env = env,
			}),
		}, metalanguage.failure_handler, nil)

		return ok, acc
	end,
	"record_desc_of_ascribed_names"
)

local record_of_ascribed_names = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: anchored_inferrable, env: Environment}|string
	function(syntax, env)
		local ok, thread = syntax:match({
			record_desc_of_ascribed_names(metalanguage.accept_handler, env),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, thread
		end
		thread.args = anchored_inferrable_term(syntax.span.start, unanchored_inferrable_term.record_type(thread.args))
		return ok, thread
	end,
	"record_of_ascribed_names"
)

local tuple_ascribed_name = ascribed_name(function(names, prev)
	return terms.binding.tuple_elim(
		names:map(name_array, function(n)
			return n.name
		end),
		names,
		prev
	)
end)

local tuple_desc_of_ascribed_names = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: spanned_name[], args: anchored_inferrable, env: Environment}|string
	function(syntax, env)
		local function build_type_term(span, args)
			return U.notail(anchored_inferrable_term(span.start, unanchored_inferrable_term.tuple_type(args)))
		end

		local names = spanned_name_array()

		local ok, acc = syntax:match({
			metalanguage.list_many_fold(function(_userdata, vals, acc)
				return true, acc
			end, function(acc, span)
				local prev = build_type_term(span, acc.args)
				return tuple_ascribed_name(function(_userdata, name, type_val, type_env)
					local names = acc.names:copy()
					names:append(name)
					local new_acc = {
						names = names,
						args = terms.inferrable_cons(
							span.start,
							acc.args,
							spanned_name("", format.span_here()),
							type_val,
							spanned_name("", format.span_here())
						),
						env = type_env,
					}
					return true, { name = name, type = type_val }, new_acc
				end, acc.env, prev, acc.names)
			end, {
				names = names,
				args = terms.inferrable_empty,
				env = env,
			}),
		}, metalanguage.failure_handler, nil)

		return ok, acc
	end,
	"tuple_desc_of_ascribed_names"
)

local tuple_of_ascribed_names = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: anchored_inferrable, env: Environment}|string
	function(syntax, env)
		local ok, thread = syntax:match({
			tuple_desc_of_ascribed_names(metalanguage.accept_handler, env),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, thread
		end
		thread.args = anchored_inferrable_term(syntax.span.start, unanchored_inferrable_term.tuple_type(thread.args))
		return ok, thread
	end,
	"tuple_of_ascribed_names"
)

local host_tuple_of_ascribed_names = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: anchored_inferrable, env: Environment}|string
	function(syntax, env)
		local ok, thread = syntax:match({
			tuple_desc_of_ascribed_names(metalanguage.accept_handler, env),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, thread
		end
		thread.args =
			anchored_inferrable_term(syntax.span.start, unanchored_inferrable_term.host_tuple_type(thread.args))
		return ok, thread
	end,
	"host_tuple_of_ascribed_names"
)

---@type lua_operative
local function record_impl(syntax, env)
	---@type boolean, ({ env: Environment, args: anchored_inferrable } | string)
	local ok, acc = syntax:match({
		record_of_ascribed_names(metalanguage.accept_handler, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, acc
	end
	---@cast acc -string
	return true, acc.args
end

local ascribed_segment = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {single: boolean, names: string|string[], args: anchored_inferrable, env: Environment}|string
	function(syntax, env)
		-- check whether syntax looks like a single annotated param
		local single, _, _, _ = syntax:match({
			metalanguage.listmatch(
				metalanguage.accept_handler,
				metalanguage.any(metalanguage.accept_handler),
				metalanguage.symbol_exact(metalanguage.accept_handler, ":"),
				metalanguage.any(metalanguage.accept_handler)
			),
		}, metalanguage.failure_handler, nil)

		local ok, thread

		if single then
			local ok, name, type_val, type_env = syntax:match({
				pure_ascribed_name(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
			if not ok then
				return ok, name
			end
			thread = { names = name, args = type_val, env = type_env }
		else
			ok, thread = syntax:match({
				tuple_of_ascribed_names(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
			if not ok then
				return ok, thread
			end
		end

		thread.single = single
		return true, thread
	end,
	"ascribed_segment"
)

local host_ascribed_segment = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {single: boolean, names: string|string[], args: anchored_inferrable, env: Environment}|string
	function(syntax, env)
		-- check whether syntax looks like a single annotated param
		local single, _, _, _ = syntax:match({
			metalanguage.listmatch(
				metalanguage.accept_handler,
				metalanguage.any(metalanguage.accept_handler),
				metalanguage.symbol_exact(metalanguage.accept_handler, ":"),
				metalanguage.any(metalanguage.accept_handler)
			),
		}, metalanguage.failure_handler, nil)

		local ok, thread

		if single then
			local ok, name, type_val, type_env = syntax:match({
				pure_ascribed_name(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
			if not ok then
				return ok, name
			end
			thread = { names = name, args = type_val, env = type_env }
		else
			ok, thread = syntax:match({
				host_tuple_of_ascribed_names(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
			if not ok then
				return ok, thread
			end
		end

		thread.single = single
		return true, thread
	end,
	"host_ascribed_segment"
)

local tuple_desc_wrap_ascribed_name = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: anchored_inferrable, env: Environment}|string
	function(syntax, env)
		local function build_type_term(start_anchor, args)
			return U.notail(anchored_inferrable_term(start_anchor, unanchored_inferrable_term.tuple_type(args)))
		end

		local names = spanned_name_array()
		local args = terms.inferrable_empty
		local debug_args = spanned_name("", format.span_here())
		local ok, name, type_val, type_env = syntax:match({
			tuple_ascribed_name(metalanguage.accept_handler, env, build_type_term(syntax.span.start, args), names),
		}, metalanguage.failure_handler, nil)
		local debug_type_val = spanned_name("", format.span_here())
		if not ok then
			return ok, name
		end

		names = names:copy()
		names:append(name)
		args = terms.inferrable_cons(syntax.span.start, args, debug_args, type_val, debug_type_val)
		env = type_env
		return ok, { names = names, args = args, env = env }
	end,
	"tuple_desc_wrap_ascribed_name"
)

local ascribed_segment_tuple_desc = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: anchored_inferrable, env: Environment}|string
	function(syntax, env)
		-- check whether syntax looks like a single annotated param
		local single, _, _, _ = syntax:match({
			metalanguage.listmatch(
				metalanguage.accept_handler,
				metalanguage.any(metalanguage.accept_handler),
				metalanguage.symbol_exact(metalanguage.accept_handler, ":"),
				metalanguage.any(metalanguage.accept_handler)
			),
		}, metalanguage.failure_handler, nil)

		local ok, thread

		if single then
			ok, thread = syntax:match({
				tuple_desc_wrap_ascribed_name(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
		else
			ok, thread = syntax:match({
				tuple_desc_of_ascribed_names(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
		end

		return ok, thread
	end,
	"ascribed_segment_tuple_desc"
)

local ascribed_segment_tuple = metalanguage.reducer(function(syntax, env)
	-- todo: instead of returning string[] return SyntaxSymbols[] to better state where terms come from
	local ok, thread = syntax:match({
		ascribed_segment_tuple_desc(metalanguage.accept_handler, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end
	thread.args = anchored_inferrable_term(syntax.span.start, unanchored_inferrable_term.tuple_type(thread.args))
	return ok, thread
end, "ascribed_segment_tuple")

local host_ascribed_segment_tuple = metalanguage.reducer(function(syntax, env)
	local ok, thread = syntax:match({
		ascribed_segment_tuple_desc(metalanguage.accept_handler, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end
	thread.args = anchored_inferrable_term(syntax.span.start, unanchored_inferrable_term.host_tuple_type(thread.args))
	return ok, thread
end, "host_ascribed_segment_tuple")

-- TODO: abstract so can reuse for func type and host func type
local function make_host_func_syntax(effectful)
	---@type lua_operative
	local function host_func_type_impl(syntax, env)
		if not env or not env.enter_block then
			error "env isn't an environment in host_func_type_impl"
		end

		local ok, params_thread, tail = syntax:match({
			metalanguage.listtail(
				metalanguage.accept_handler,
				host_ascribed_segment(metalanguage.accept_handler, env),
				metalanguage.symbol_exact(metalanguage.accept_handler, "->")
			),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, params_thread
		end
		local params_single = params_thread.single
		local params_args = params_thread.args
		local params_info = params_thread.names
		env = params_thread.env

		--print("moving on to return type")

		local shadowed
		shadowed, env = env:enter_block(terms.block_purity.pure)
		-- tail.start_anchor can be nil so we fall back to the start_anchor for this host func type if needed
		-- TODO: use correct name in lambda parameter instead of adding an extra let

		local start_anchor = (tail.span.start or syntax.span.start)

		ok, env = env:bind_local(
			terms.binding.annotated_lambda(
				"#host-func-arguments",
				params_args,
				start_anchor,
				terms.visibility.explicit,
				literal_purity_pure
			)
		)
		if not ok then
			return false, env
		end
		local ok, arg = env:get("#host-func-arguments")
		if not ok then
			error("wtf")
		end
		---@cast arg -string
		if params_single then
			ok, env = env:bind_local(terms.binding.let(params_info.name, params_info, arg))
		else
			ok, env = env:bind_local(terms.binding.tuple_elim(
				params_info:map(name_array, function(n)
					return n.name
				end),
				params_info,
				arg
			))
		end
		if not ok then
			return false, env
		end

		local ok, results_thread = tail:match({
			metalanguage.listmatch(
				metalanguage.accept_handler,
				host_ascribed_segment(metalanguage.accept_handler, env)
			),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, results_thread
		end

		local results_args = results_thread.args
		env = results_thread.env

		if effectful then
			local effect_description = strict_value.effect_row(gen.declare_set(terms.unique_id)(terms.lua_prog))
			local effect_term = anchored_inferrable_term(
				start_anchor,
				unanchored_inferrable_term.typed(
					typed_term.literal(strict_value.effect_row_type),
					usage_array(),
					typed_term.literal(effect_description)
				)
			)

			results_args = anchored_inferrable_term(
				start_anchor,
				unanchored_inferrable_term.program_type(effect_term, results_args)
			)
		end

		local env, fn_res_term, purity = env:exit_block(results_args, shadowed)
		local fn_type_term = anchored_inferrable_term(
			start_anchor,
			unanchored_inferrable_term.host_function_type(
				params_args,
				fn_res_term,
				terms.checkable_term.inferrable(
					anchored_inferrable_term(
						start_anchor,
						unanchored_inferrable_term.typed(
							typed_term.literal(strict_value.result_info_type),
							usage_array(),
							typed_term.literal(effectful and result_info_effectful or result_info_pure)
						)
					)
				)
			)
		)

		--print("reached end of function type construction")
		if not env.enter_block then
			error "env isn't an environment at end in host_func_type_impl"
		end
		return true, fn_type_term, env
	end

	return host_func_type_impl
end

-- TODO: abstract so can reuse for func type and host func type
---@type lua_operative
local function forall_impl(syntax, env)
	if not env or not env.enter_block then
		error "env isn't an environment in forall_impl"
	end

	local ok, params_thread, tail = syntax:match({
		metalanguage.listtail(
			metalanguage.accept_handler,
			ascribed_segment(metalanguage.accept_handler, env),
			metalanguage.symbol_exact(metalanguage.accept_handler, "->")
		),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, params_thread
	end
	local params_single = params_thread.single
	local params_args = params_thread.args
	local params_info = params_thread.names
	local params_names
	env = params_thread.env
	---@cast env Environment
	--print("moving on to return type")

	local shadowed, inner_name
	shadowed, env = env:enter_block(terms.block_purity.pure)
	-- tail.start_anchor can be nil so we fall back to the start_anchor for this forall type if needed
	-- TODO: use correct name in lambda parameter instead of adding an extra let
	if params_single then
		params_names = params_info.name
		inner_name = "forall(" .. params_names .. ")"
	else
		params_names = params_info:map(name_array, function(n)
			return n.name
		end)
		inner_name = "forall(" .. table.concat(params_names, ", ") .. ")"
	end

	local start_anchor = tail.span.start or syntax.span.start

	ok, env = env:bind_local(
		terms.binding.annotated_lambda(
			inner_name,
			params_args,
			start_anchor,
			terms.visibility.explicit,
			literal_purity_pure
		)
	)
	if not ok then
		return false, env
	end
	local ok, arg = env:get(inner_name)
	if not ok then
		error("wtf")
	end
	---@cast arg -string
	if params_single then
		ok, env = env:bind_local(terms.binding.let(params_names, params_info, arg))
	else
		ok, env = env:bind_local(terms.binding.tuple_elim(params_names, params_info, arg))
	end
	if not ok then
		return false, env
	end
	local ok, results_thread = tail:match({
		metalanguage.listmatch(metalanguage.accept_handler, ascribed_segment(metalanguage.accept_handler, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, results_thread
	end

	local results_args = results_thread.args
	env = results_thread.env
	---@cast env Environment

	local env, fn_res_term, purity = env:exit_block(results_args, shadowed)

	local fn_type_term = anchored_inferrable_term(
		start_anchor,
		unanchored_inferrable_term.pi(
			params_args,
			terms.checkable_term.inferrable(
				anchored_inferrable_term(
					start_anchor,
					unanchored_inferrable_term.typed(
						typed_term.literal(strict_value.param_info_type),
						usage_array(),
						typed_term.literal(param_info_explicit)
					)
				)
			),
			fn_res_term,
			terms.checkable_term.inferrable(
				anchored_inferrable_term(
					start_anchor,
					unanchored_inferrable_term.typed(
						typed_term.literal(strict_value.result_info_type),
						usage_array(),
						typed_term.literal(result_info_pure)
					)
				)
			)
		)
	)

	--print("reached end of function type construction")
	if not env.enter_block then
		error "env isn't an environment at end in forall_impl"
	end
	return true, fn_type_term, env
end

---Constrains a type by using a checked expression goal and producing an annotated inferrable term
---(the host-number 5) -> produces inferrable_term.annotated(lit(5), lit(host-number))
---@type lua_operative
local function the_operative_impl(syntax, env)
	local ok, type_inferrable_term, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, exprs.inferred_expression(metalanguage.accept_handler, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, type_inferrable_term, tail
	end

	local ok, type_of_typed_term, usages, type_typed_term =
		evaluator.infer(type_inferrable_term, env.typechecking_context)
	if not ok then
		return false, type_of_typed_term
	end

	local evaled_type =
		evaluator.evaluate(type_typed_term, env.typechecking_context.runtime_context, env.typechecking_context)

	--print("type_inferrable_term: (inferrable term follows)")
	--print(type_inferrable_term:pretty_print(env.typechecking_context))
	--print("evaled_type: (value term follows)")
	--print(evaled_type)
	--print("tail", tail)
	local ok, val, tail = tail:match({
		metalanguage.ispair(metalanguage.accept_handler),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return false, val
	end
	local ok, val, env = val:match({
		exprs.expression(
			metalanguage.accept_handler,
			-- FIXME: do we infer here if evaled_type is stuck / a placeholder?
			exprs.ExpressionArgs.new(terms.expression_goal.check(evaled_type), env)
		),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, val
	end
	if terms.checkable_term.value_check(val) ~= true then
		print("val", val)
		error "the operative didn't get a checkable term"
	end
	return ok,
		U.notail(

			anchored_inferrable_term(syntax.span.start, unanchored_inferrable_term.annotated(val, type_inferrable_term)),
			env
		)
end

---apply(fn, args) calls fn with an existing args tuple
---@type lua_operative
local function apply_operative_impl(syntax, env)
	local ok, fn, tail =
		syntax:match({ metalanguage.ispair(metalanguage.accept_handler) }, metalanguage.failure_handler, nil)
	if not ok then
		return ok, fn
	end

	local ok, fn_inferrable_term, env =
		fn:match({ exprs.inferred_expression(metalanguage.accept_handler, env) }, metalanguage.failure_handler, nil)
	if not ok then
		return ok, fn_inferrable_term
	end

	local ok, type_of_fn, usages, fn_typed_term = evaluator.infer(fn_inferrable_term, env.typechecking_context)
	if not ok then
		return ok, type_of_fn
	end

	-- TODO: apply operative?
	-- TODO: param info and result info
	local param_type_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
	--local param_info_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
	local result_type_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
	--local result_info_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
	local param_type = param_type_mv:as_flex()
	--local param_info = param_info_type_mv:as_flex()
	local param_info = flex_value.strict(param_info_explicit)
	local result_type = result_type_mv:as_flex()
	--local result_info = result_info_type_mv:as_flex()
	local result_info = flex_value.strict(result_info_pure)
	local spec_type = flex_value.pi(param_type, param_info, result_type, result_info)
	local host_spec_type = flex_value.host_function_type(param_type, result_type, result_info)

	local function apply_inner(spec_type)
		local ok, err = evaluator.typechecker_state:speculate(function()
			return evaluator.typechecker_state:flow(
				type_of_fn,
				env.typechecking_context,
				spec_type,
				env.typechecking_context,
				terms.constraintcause.primitive("apply", format.anchor_here())
			)
		end)
		if not ok then
			return false, err
		end

		local ok, args_inferrable_term = tail:match({
			metalanguage.listmatch(
				metalanguage.accept_handler,
				exprs.expression(
					utils.accept_with_env,
					-- FIXME: do we infer here if evaled_type is stuck / a placeholder?
					exprs.ExpressionArgs.new(terms.expression_goal.check(param_type), env)
				)
			),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, args_inferrable_term
		end

		local inf_term, env = utils.unpack_val_env(args_inferrable_term)
		return true,
			U.notail(
				anchored_inferrable_term(
					syntax.span.start,
					unanchored_inferrable_term.application(
						anchored_inferrable_term(
							syntax.span.start,
							unanchored_inferrable_term.typed(
								evaluator.substitute_placeholders_identity(spec_type, env.typechecking_context),
								usages,
								fn_typed_term
							)
						),

						inf_term
					)
				)
			),
			env
	end

	local ok, res1, res1env, res2, res2env
	ok, res1, res1env = apply_inner(spec_type)
	if ok then
		return true, res1, res1env
	end
	ok, res2, res2env = apply_inner(host_spec_type)
	if ok then
		return true, res2, res2env
	end
	--error(res1)
	--error(res2)
	-- try uncommenting one of the error prints above
	-- you need to figure out which one is relevant for your problem
	-- after you're finished, please comment it out so that, next time, the message below can be found again
	error("apply() speculation failed! debugging this is left as an exercise to the maintainer")
end

---@type lua_operative
local function lambda_impl(syntax, env)
	local ok, thread, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, ascribed_segment_tuple(metalanguage.accept_handler, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end

	local args, info, env = thread.args, thread.names, thread.env
	local names = info:map(name_array, function(n)
		return n.name
	end)
	local shadow, inner_env = env:enter_block(terms.block_purity.pure)
	local inner_name = "λ(" .. table.concat(names, ",") .. ")"
	ok, inner_env = inner_env:bind_local(
		terms.binding.annotated_lambda(
			inner_name,
			args,
			syntax.span.start,
			terms.visibility.explicit,
			literal_purity_pure
		)
	)
	if not ok then
		return false, inner_env
	end
	local _, arg = inner_env:get(inner_name)
	ok, inner_env = inner_env:bind_local(terms.binding.tuple_elim(names, info, arg))
	if not ok then
		return false, inner_env
	end
	local ok, expr, env = tail:match(
		{ exprs.block(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, inner_env)) },
		metalanguage.failure_handler,
		nil
	)
	if not ok then
		return ok, expr
	end
	local resenv, term, purity = env:exit_block(expr, shadow)
	return true, term, resenv
end

---@type lua_operative
local function lambda_prog_impl(syntax, env)
	local ok, thread, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, ascribed_segment_tuple(metalanguage.accept_handler, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end

	local args, info, env = thread.args, thread.names, thread.env
	local names = info:map(name_array, function(n)
		return n.name
	end)
	local inner_name = "λ-prog(" .. table.concat(names, ",") .. ")"

	local shadow, inner_env = env:enter_block(terms.block_purity.effectful)
	ok, inner_env = inner_env:bind_local(
		terms.binding.annotated_lambda(
			inner_name,
			args,
			syntax.span.start,
			terms.visibility.explicit,
			literal_purity_effectful
		)
	)
	if not ok then
		return false, inner_env
	end
	local _, arg = inner_env:get(inner_name)
	ok, inner_env = inner_env:bind_local(terms.binding.tuple_elim(names, info, arg))
	if not ok then
		return false, inner_env
	end
	local ok, expr, env = tail:match(
		{ exprs.block(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, inner_env)) },
		metalanguage.failure_handler,
		nil
	)
	if not ok then
		return ok, expr
	end
	local resenv, term, purity = env:exit_block(expr, shadow)
	return true, term, resenv
end

---@type lua_operative
local function lambda_single_impl(syntax, env)
	local ok, thread, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, pure_ascribed_name(utils.accept_bundled, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end

	local name, arg, env = utils.unpack_bundle(thread)

	local shadow, inner_env = env:enter_block(terms.block_purity.pure)
	ok, inner_env = inner_env:bind_local(
		terms.binding.annotated_lambda(
			name.name,
			arg,
			syntax.span.start,
			terms.visibility.explicit,
			literal_purity_pure
		)
	)
	if not ok then
		return false, inner_env
	end
	local ok, expr, env = tail:match(
		{ exprs.block(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, inner_env)) },
		metalanguage.failure_handler,
		nil
	)
	if not ok then
		return ok, expr
	end
	local resenv, term, purity = env:exit_block(expr, shadow)
	return true, term, resenv
end

-- TODO: de-duplicate with above function by wrapping in constructor that takes an implicit or explicit visibility
---@type lua_operative
local function lambda_implicit_impl(syntax, env)
	local ok, thread, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, pure_ascribed_name(utils.accept_bundled, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end

	local name, arg, env = utils.unpack_bundle(thread)

	local shadow, inner_env = env:enter_block(terms.block_purity.pure)
	ok, inner_env = inner_env:bind_local(
		terms.binding.annotated_lambda(
			name.name,
			arg,
			syntax.span.start,
			terms.visibility.implicit,
			literal_purity_pure
		)
	)
	if not ok then
		return false, inner_env
	end
	local ok, expr, env = tail:match(
		{ exprs.block(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, inner_env)) },
		metalanguage.failure_handler,
		nil
	)
	if not ok then
		return ok, expr
	end
	local resenv, term, purity = env:exit_block(expr, shadow)
	terms.verify_placeholder_lite(term, resenv.typechecking_context, false) --DEBUG: check if a placeholder is leaking. remove after tests pass
	return true, term, resenv
end

---@type lua_operative
local function lambda_annotated_impl(syntax, env)
	local ok, thread, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, ascribed_segment_tuple(metalanguage.accept_handler, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end

	local args, info, env = thread.args, thread.names, thread.env
	local names = info:map(name_array, function(n)
		return n.name
	end)
	local inner_name = "λ-named(" .. table.concat(names, ",") .. ")"

	local shadow, inner_env = env:enter_block(terms.block_purity.pure)
	ok, inner_env = inner_env:bind_local(
		terms.binding.annotated_lambda(
			inner_name,
			args,
			syntax.span.start,
			terms.visibility.explicit,
			literal_purity_pure
		)
	)
	if not ok then
		return false, inner_env
	end
	local _, arg = inner_env:get(inner_name)
	ok, inner_env = inner_env:bind_local(terms.binding.tuple_elim(names, info, arg))
	if not ok then
		return false, inner_env
	end
	local ok, ann_expr_env, tail = tail:match({
		metalanguage.listtail(
			metalanguage.accept_handler,
			metalanguage.symbol_exact(metalanguage.accept_handler, ":"),
			exprs.inferred_expression(utils.accept_with_env, inner_env)
		),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, ann_expr_env
	end
	local ann_expr, inner_env = utils.unpack_val_env(ann_expr_env)

	local ok, expr, env = tail:match(
		{ exprs.block(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, inner_env)) },
		metalanguage.failure_handler,
		nil
	)
	if not ok then
		return ok, expr
	end
	expr = anchored_inferrable_term(
		syntax.span.start,
		unanchored_inferrable_term.annotated(terms.checkable_term.inferrable(expr), ann_expr)
	)
	local resenv, term, purity = env:exit_block(expr, shadow)
	return true, term, resenv
end

---@type lua_operative
local function startype_impl(syntax, env)
	local ok, level_val, depth_val = syntax:match({
		metalanguage.listmatch(
			metalanguage.accept_handler,
			metalanguage.isvalue(metalanguage.accept_handler),
			metalanguage.isvalue(metalanguage.accept_handler)
		),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, level_val
	end
	if level_val.type ~= "f64" then
		return false, "literal must be a number for type levels"
	end
	if level_val.val % 1 ~= 0 then
		return false, "literal must be an integer for type levels"
	end
	if depth_val.type ~= "f64" then
		return false, "literal must be a number for type levels"
	end
	if depth_val.val % 1 ~= 0 then
		return false, "literal must be an integer for type levels"
	end
	local term = anchored_inferrable_term(
		syntax.span.start,
		unanchored_inferrable_term.typed(
			typed_term.literal(strict_value.star(level_val.val + 1, depth_val.val + 1)),
			usage_array(),
			typed_term.star(level_val.val, depth_val.val)
		)
	)

	return true, term, env
end

---@param goal goal
---@return strict_value
local function host_term_of_inner(goal)
	if goal:is_infer() then
		return terms.host_inferrable_term_type
	elseif goal:is_check() then
		return terms.host_checkable_term_type
	else
		error("host_term_of_inner: unknown goal")
	end
end

local host_term_of_inner_type = strict_value.host_function_type(
	strict_value.host_tuple_type(
		terms.strict_tuple_desc(
			strict_value.closure(
				"#htoit-empty",
				typed_term.literal(terms.host_goal_type),
				empty_tuple,
				spanned_name("", format.span_here()),
				spanned_name("", format.span_here())
			)
		)
	),
	strict_value.closure(
		"#htoit-params",
		typed_term.literal(
			strict_value.host_tuple_type(
				terms.strict_tuple_desc(
					strict_value.closure(
						"#htoit-empty",
						typed_term.host_wrapped_type(typed_term.literal(strict_value.host_type_type)),
						empty_tuple,
						spanned_name("", format.span_here()),
						spanned_name("", format.span_here())
					)
				)
			)
		),
		empty_tuple,
		spanned_name("", format.span_here()),
		spanned_name("", format.span_here())
	),
	result_info_pure
)

---@param goal typed
---@param context_len integer
---@return typed
local function host_term_of(goal, context_len)
	local t = name_array("#host_term_of-t")
	return U.notail(
		typed_term.tuple_elim(
			t,
			t:map(spanned_name_array, function(n)
				return spanned_name(n, format.span_here())
			end),
			typed_term.application(
				typed_term.literal(strict_value.host_value(host_term_of_inner)),
				typed_term.host_tuple_cons(typed_term_array(goal))
			),
			1,
			typed_term.host_unwrap(typed_term.bound_variable(context_len + 1, spanned_name("", format.span_here())))
		)
	)
end

---@param ud_type strict_value
---@param span Span
---@return strict_value
local function operative_handler_type(ud_type, span)
	local namesp4 = name_array(
		spanned_name("#operative_handler_type-syn", span),
		spanned_name("#operative_handler_type-env", span),
		spanned_name("#operative_handler_type-ud", span),
		spanned_name("#operative_handler_type-goal", span)
	)
	local pnamep0 = spanned_name("#operative_handler_type-empty", span)
	local pnamep1 = spanned_name("#operative_handler_type-syn", span)
	local pnamep2 = spanned_name("#operative_handler_type-syn-env", span)
	local pnamep3 = spanned_name("#operative_handler_type-syn-env-ud", span)
	local pnamer = spanned_name("#operative_handler_type-params", span)
	local pnamer0 = spanned_name("#operative_handler_type-result-empty", span)
	local pnamer1 = spanned_name("#operative_handler_type-result-term", span)
	local capture_dbg = spanned_name("#capture", span)
	return U.notail(
		strict_value.pi(
			strict_value.tuple_type(
				terms.strict_tuple_desc(
					strict_value.closure(
						pnamep0.name,
						typed_term.literal(terms.host_syntax_type),
						empty_tuple,
						spanned_name("", format.span_here()),
						pnamep0
					),
					strict_value.closure(
						pnamep1.name,
						typed_term.literal(terms.host_environment_type),
						empty_tuple,
						spanned_name("", format.span_here()),
						pnamep1
					),
					strict_value.closure(
						pnamep2.name,
						typed_term.literal(ud_type),
						empty_tuple,
						spanned_name("", format.span_here()),
						pnamep2
					),
					strict_value.closure(
						pnamep3.name,
						typed_term.literal(terms.host_goal_type),
						empty_tuple,
						spanned_name("", format.span_here()),
						pnamep3
					)
				)
			),
			param_info_explicit,
			strict_value.closure(
				pnamer.name,
				typed_term.tuple_elim(
					namesp4:map(name_array, function(d)
						return d.name
					end),
					namesp4,
					typed_term.bound_variable(2, pnamer),
					4,
					typed_term.tuple_type(
						terms.typed_tuple_desc(
							typed_term.lambda(
								pnamer0.name,
								pnamer0,
								host_term_of(
									typed_term.tuple_element_access(typed_term.bound_variable(1, capture), 1),
									6
								),
								typed_term.tuple_cons(typed_term_array(typed_term.bound_variable(6, pnamer0))),
								capture_dbg,
								anchor
							),
							typed_term.lambda(
								pnamer1.name,
								pnamer1,
								typed_term.literal(terms.host_environment_type),
								typed_term.tuple_cons(typed_term_array()),
								spanned_name("", format.span_here()),
								anchor
							)
						)
					)
				),
				empty_tuple,
				spanned_name("", format.span_here()),
				pnamer
			),
			result_info_pure
		)
	)
end

---@type lua_operative
local function into_operative_impl(syntax, env)
	local ok, ud_type_syntax, ud_syntax, handler_syntax = syntax:match({
		metalanguage.listmatch(
			metalanguage.accept_handler,
			metalanguage.any(metalanguage.accept_handler),
			metalanguage.any(metalanguage.accept_handler),
			metalanguage.any(metalanguage.accept_handler)
		),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return false, ud_type_syntax
	end

	local ok, ud_type_chk, env = ud_type_syntax:match({
		exprs.expression(
			metalanguage.accept_handler,
			exprs.ExpressionArgs.new(terms.expression_goal.check(strict_value.host_type_type), env)
		),
	}, metalanguage.failure_handler)
	if not ok then
		return false, ud_type_chk
	end
	local ok, ud_type_usages, ud_type_t =
		evaluator.check(ud_type_chk, env.typechecking_context, strict_value.host_type_type)
	if not ok then
		return false, ud_type_usages
	end
	local ud_type = evaluator.evaluate(ud_type_t, env.typechecking_context.runtime_context, env.typechecking_context)

	local ok, ud_chk, env = ud_syntax:match({
		exprs.expression(
			metalanguage.accept_handler,
			exprs.ExpressionArgs.new(terms.expression_goal.check(ud_type), env)
		),
	}, metalanguage.failure_handler)
	if not ok then
		return false, ud_chk
	end
	local ok, ud_usages, ud_t = evaluator.check(ud_chk, env.typechecking_context, ud_type)
	if not ok then
		return false, ud_usages
	end
	local ud = evaluator.evaluate(ud_t, env.typechecking_context.runtime_context, env.typechecking_context)

	local ok, handler_chk, env = handler_syntax:match({
		exprs.expression(
			metalanguage.accept_handler,
			exprs.ExpressionArgs.new(
				terms.expression_goal.check(operative_handler_type(ud_type, syntax.span.start)),
				env
			)
		),
	}, metalanguage.failure_handler)
	if not ok then
		return false, handler_chk
	end
	local ok, handler_usages, handler_t =
		evaluator.check(handler_chk, env.typechecking_context, operative_handler_type(ud_type, syntax.span.start))
	if not ok then
		return false, handler_usages
	end
	local handler = evaluator.evaluate(handler_t, env.typechecking_context.runtime_context, env.typechecking_context)

	local op_type = flex_value.operative_type(handler, ud_type)
	local op_val = flex_value.operative_value(ud)

	return true,
		U.notail(

			anchored_inferrable_term(
				syntax.span.start,
				unanchored_inferrable_term.typed(op_type, usage_array(), typed_term.literal(op_val))
			)
		),
		env
end

-- eg typed.host_wrap, typed.host_wrapped_type
---@param body_fn fun(typed): typed
---@param type_fn fun(typed): typed
---@return anchored_inferrable
local function build_wrap(body_fn, type_fn)
	local names = gen.declare_array(gen.builtin_string)
	local names0 = names()
	local names1 = names("#wrap-TODO1")
	local names2 = names("#wrap-TODO1", "#wrap-TODO2")
	local pname_arg = "#wrap-arguments"
	local pname_type = "#wrap-prev"
	local args_dbg = spanned_name("#args", format.span_here())
	local args0_dbg = spanned_name("#args0", format.span_here())
	local args1_dbg = spanned_name("#args1", format.span_here())
	local univ_dbg = spanned_name("#univ", format.span_here())
	local subj_dbg = spanned_name("#subj", format.span_here())
	return U.notail(
		lit_term(
			strict_value.closure(
				pname_arg,
				typed_term.tuple_elim(
					names2,
					spanned_name_array(univ_dbg, subj_dbg),
					typed_term.bound_variable(2, args_dbg),
					2,
					body_fn(typed_term.bound_variable(4, subj_dbg))
				),
				empty_tuple,
				spanned_name("", format.span_here()),
				args_dbg
			),
			strict_value.pi(
				strict_value.tuple_type(
					terms.strict_tuple_desc(
						strict_value.closure(
							pname_type,
							typed_term.tuple_elim(
								names0,
								spanned_name_array(),
								typed_term.bound_variable(2, args0_dbg),
								0,
								typed_term.star(evaluator.OMEGA + 1, 0)
							),
							empty_tuple,
							spanned_name("", format.span_here()),
							args0_dbg
						),
						strict_value.closure(
							pname_type,
							typed_term.tuple_elim(
								names1,
								spanned_name_array(univ_dbg),
								typed_term.bound_variable(2, args1_dbg),
								1,
								typed_term.bound_variable(3, univ_dbg)
							),
							empty_tuple,
							spanned_name("", format.span_here()),
							args1_dbg
						)
					)
				),
				param_info_explicit,
				strict_value.closure(
					pname_type,
					typed_term.tuple_elim(
						names2,
						spanned_name_array(univ_dbg, subj_dbg),
						typed_term.bound_variable(2, args_dbg),
						2,
						type_fn(typed_term.bound_variable(3, univ_dbg))
					),
					empty_tuple,
					spanned_name("", format.span_here()),
					args_dbg
				),
				result_info_pure
			)
		)
	)
end

-- eg typed.host_unwrap, typed.host_wrapped_type
---@param body_fn fun(typed): typed
---@param type_fn fun(typed): typed
---@return anchored_inferrable
local function build_unwrap(body_fn, type_fn)
	local names = gen.declare_array(gen.builtin_string)
	local names0 = names()
	local names1 = names("#unwrap-TODO1")
	local names2 = names("#unwrap-TODO1", "#unwrap-TODO2")
	local pname_arg = "#unwrap-arguments"
	local pname_type = "#unwrap-prev"
	local args_dbg = spanned_name("#args", format.span_here())
	local args0_dbg = spanned_name("#args0", format.span_here())
	local args1_dbg = spanned_name("#args1", format.span_here())
	local univ_dbg = spanned_name("#univ", format.span_here())
	local subj_dbg = spanned_name("#subj", format.span_here())
	return U.notail(
		lit_term(
			strict_value.closure(
				pname_arg,
				typed_term.tuple_elim(
					names2,
					spanned_name_array(univ_dbg, subj_dbg),
					typed_term.bound_variable(2, args_dbg),
					2,
					body_fn(typed_term.bound_variable(4, subj_dbg))
				),
				empty_tuple,
				spanned_name("", format.span_here()),
				args_dbg
			),
			strict_value.pi(
				strict_value.tuple_type(
					terms.strict_tuple_desc(
						strict_value.closure(
							pname_type,
							typed_term.tuple_elim(
								names0,
								spanned_name_array(),
								typed_term.bound_variable(2, args0_dbg),
								0,
								typed_term.star(evaluator.OMEGA + 1, 0)
							),
							empty_tuple,
							spanned_name("", format.span_here()),
							args0_dbg
						),
						strict_value.closure(
							pname_type,
							typed_term.tuple_elim(
								names1,
								spanned_name_array(univ_dbg),
								typed_term.bound_variable(2, args1_dbg),
								1,
								type_fn(typed_term.bound_variable(3, univ_dbg))
							),
							empty_tuple,
							spanned_name("", format.span_here()),
							args1_dbg
						)
					)
				),
				param_info_explicit,
				strict_value.closure(
					pname_type,
					typed_term.tuple_elim(
						names2,
						spanned_name_array(univ_dbg, subj_dbg),
						typed_term.bound_variable(2, args_dbg),
						2,
						typed_term.bound_variable(3, univ_dbg)
					),
					empty_tuple,
					spanned_name("", format.span_here()),
					args_dbg
				),
				result_info_pure
			)
		)
	)
end

-- eg typed.host_wrapped_type,
---@param body_fn fun(typed): typed
---@return anchored_inferrable
local function build_wrapped(body_fn)
	local names = gen.declare_array(gen.builtin_string)
	local names0 = names()
	local names1 = names("#wrapped-TODO1")
	local pname_arg = "#wrapped-arguments"
	local pname_type = "#wrapped-prev"
	local args_dbg = spanned_name("#args", format.span_here())
	local args0_dbg = spanned_name("#args0", format.span_here())
	local typ_dbg = spanned_name("#typ", format.span_here())
	return U.notail(
		lit_term(
			strict_value.closure(
				pname_arg,
				typed_term.tuple_elim(
					names1,
					spanned_name_array(typ_dbg),
					typed_term.bound_variable(2, args_dbg),
					1,
					body_fn(typed_term.bound_variable(3, typ_dbg))
				),
				empty_tuple,
				spanned_name("", format.span_here()),
				args_dbg
			),
			strict_value.pi(
				strict_value.tuple_type(
					terms.strict_tuple_desc(
						strict_value.closure(
							pname_type,
							typed_term.tuple_elim(
								names0,
								spanned_name_array(),
								typed_term.bound_variable(2, args0_dbg),
								0,
								typed_term.star(evaluator.OMEGA + 1, 0)
							),
							empty_tuple,
							spanned_name("", format.span_here()),
							args0_dbg
						)
					)
				),
				param_info_explicit,
				strict_value.closure(
					pname_type,
					typed_term.tuple_elim(
						names1,
						spanned_name_array(typ_dbg),
						typed_term.bound_variable(2, args_dbg),
						1,
						typed_term.literal(strict_value.host_type_type)
					),
					empty_tuple,
					spanned_name("", format.span_here()),
					args_dbg
				),
				result_info_pure
			)
		)
	)
end

---@param env Environment
local enum_variant = metalanguage.reducer(function(syntax, env)
	local ok, tag, tail = syntax:match({
		metalanguage.listtail(
			metalanguage.accept_handler,
			metalanguage.issymbol(metalanguage.accept_handler),
			ascribed_segment_tuple_desc(metalanguage.accept_handler, env)
		),
	}, metalanguage.failure_handler, nil)

	if not ok then
		return ok, tag
	end

	if not tag then
		return false, "missing enum variant name"
	end

	return true,
		tag.name,
		U.notail(anchored_inferrable_term(syntax.span.start, unanchored_inferrable_term.tuple_type(tail.args))),
		env
end, "enum_variant")

---@type lua_operative
local function enum_impl(syntax, env)
	local variants = gen.declare_map(gen.builtin_string, anchored_inferrable_term)()
	while not syntax:match({ metalanguage.isnil(metalanguage.accept_handler) }, metalanguage.failure_handler, nil) do
		local tag, term

		ok, tag, syntax = syntax:match({
			metalanguage.listtail(metalanguage.accept_handler, enum_variant(utils.accept_bundled, env)),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, tag
		end

		tag, term = table.unpack(tag)
		variants:set(tag, term)
	end

	return true,
		U.notail(
			anchored_inferrable_term(
				syntax.span.start,
				unanchored_inferrable_term.enum_type(

					anchored_inferrable_term(
						syntax.span.start,
						unanchored_inferrable_term.enum_desc_cons(
							variants,
							anchored_inferrable_term(
								syntax.span.start,
								unanchored_inferrable_term.typed(
									typed_term.literal(strict_value.enum_desc_type(strict_value.star(0, 0))),
									usage_array(),
									typed_term.literal(
										strict_value.enum_desc_value(
											gen.declare_map(gen.builtin_string, terms.flex_value)()
										)
									)
								)
							)
						)
					)
				)
			)
		),
		env
end

---@type lua_operative
local function debug_trace_impl(syntax, env)
	local ok, term_env = syntax:match({
		metalanguage.listmatch(metalanguage.accept_handler, exprs.inferred_expression(utils.accept_bundled, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, term_env
	end
	local term, env = utils.unpack_bundle(term_env)

	--term.track = true
	return ok, term, env
end

---@type lua_operative
local function dump_context_impl(syntax, env)
	print("\nDUMP CONTEXT:")
	print(env.typechecking_context:format_names_and_types())
	local ok, term_env = syntax:match({
		metalanguage.listmatch(metalanguage.accept_handler, exprs.inferred_expression(utils.accept_bundled, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, term_env
	end
	local term, env = utils.unpack_bundle(term_env)

	return ok, term, env
end

local last_snapshot
---@type lua_operative
local function graph_snapshot_start_impl(syntax, env)
	last_snapshot = evaluator.typechecker_state:Snapshot("user request")
	return true,
		anchored_inferrable_term(
			syntax.span.start,
			unanchored_inferrable_term.tuple_cons(anchored_inferrable_term_array(), spanned_name_array())
		),
		env
end
---@type lua_operative
local function graph_snapshot_dump_impl(syntax, env)
	local ok, name = syntax:match({
		metalanguage.listmatch(metalanguage.accept_handler, metalanguage.isvalue(metalanguage.accept_handler)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, name
	end
	if not name.type == "string" then
		return false, "needs to provide string for graph file name"
	end
	local f = io.open(name.val .. ".dot", "w")
	evaluator.typechecker_state:Visualize(f, last_snapshot)
	f:close()
	return true,
		anchored_inferrable_term(
			syntax.span.start,
			unanchored_inferrable_term.tuple_cons(anchored_inferrable_term_array(), spanned_name_array())
		),
		env
end

local core_operations = {
	--["do"] = evaluator.host_operative(do_block),
	let = exprs.host_operative(let_impl, "let_impl"),
	mk = exprs.host_operative(mk_impl, "mk_impl"),
	switch = exprs.host_operative(switch_impl, "switch_impl"),
	enum = exprs.host_operative(enum_impl, "enum_impl"),
	["debug-trace"] = exprs.host_operative(debug_trace_impl, "debug_trace_impl"),
	["dump-context"] = exprs.host_operative(dump_context_impl, "dump_context_impl"),
	["graph-snapshot-start"] = exprs.host_operative(graph_snapshot_start_impl, "graph_snapshot_start_impl"),
	["graph-snapshot-dump"] = exprs.host_operative(graph_snapshot_dump_impl, "graph_snapshot_dump_impl"),
	intrinsic = exprs.host_operative(intrinsic_impl, "intrinsic_impl"),
	["host-number"] = lit_term(strict_value.host_number_type, strict_value.host_type_type),
	["host-type"] = lit_term(strict_value.host_type_type, strict_value.star(1, 1)),
	["host-func-type"] = exprs.host_operative(make_host_func_syntax(false), "host_func_type_impl"),
	["host-prog-type"] = exprs.host_operative(make_host_func_syntax(true), "host_prog_type_impl"),
	type = lit_term(strict_value.star(0, 0), strict_value.star(1, 1)),
	type_ = exprs.host_operative(startype_impl, "startype_impl"),
	["forall"] = exprs.host_operative(forall_impl, "forall_impl"),
	lambda = exprs.host_operative(lambda_impl, "lambda_impl"),
	lambda_single = exprs.host_operative(lambda_single_impl, "lambda_single_impl"),
	["lambda-prog"] = exprs.host_operative(lambda_prog_impl, "lambda_prog_impl"),
	lambda_implicit = exprs.host_operative(lambda_implicit_impl, "lambda_implicit_impl"),
	lambda_curry = exprs.host_operative(lambda_curry_impl, "lambda_curry_impl"),
	lambda_annotated = exprs.host_operative(lambda_annotated_impl, "lambda_annotated_impl"),
	the = exprs.host_operative(the_operative_impl, "the"),
	apply = exprs.host_operative(apply_operative_impl, "apply"),
	wrap = build_wrap(typed_term.host_wrap, typed_term.host_wrapped_type),
	["unstrict-wrap"] = build_wrap(typed_term.host_unstrict_wrap, typed_term.host_unstrict_wrapped_type),
	wrapped = build_wrapped(typed_term.host_wrapped_type),
	["unstrict-wrapped"] = build_wrapped(typed_term.host_unstrict_wrapped_type),
	unwrap = build_unwrap(typed_term.host_unwrap, typed_term.host_wrapped_type),
	["unstrict-unwrap"] = build_unwrap(typed_term.host_unstrict_unwrap, typed_term.host_unstrict_wrapped_type),
	["record"] = exprs.host_operative(record_impl, "record"),
	["record-of"] = exprs.host_operative(record_of_impl, "record-of"),
	--["dump-env"] = evaluator.host_operative(function(syntax, env) print(environment.dump_env(env)); return true, types.unit_val, env end),
	--["basic-fn"] = evaluator.host_operative(basic_fn),
	--tuple = evaluator.host_operative(tuple_type_impl),
	--["tuple-of"] = evaluator.host_operative(tuple_of_impl),
	--number = { type = types.type, val = types.number }
	-- ["into-operative"] = exprs.host_operative(into_operative_impl, "into_operative_impl"),
	-- ["hackhack-host-term-of-inner"] = anchored_inferrable_term(
	-- 	format.anchor_here(),
	-- 	unanchored_inferrable_term.typed(
	-- 		host_term_of_inner_type,
	-- 		usage_array(),
	-- 		typed_term.literal(value.host_value(host_term_of_inner))
	-- 	)
	-- ),
}

-- FIXME: use these once reimplemented with terms
--local modules = require "modules"
--local cotuple = require "cotuple"

local function create()
	local env = environment.new_env {
		nonlocals = trie.build(core_operations),
	}
	-- p(env)
	-- p(modules.mod)
	--env = modules.use_mod(modules.module_mod, env)
	--env = modules.use_mod(cotuple.cotuple_module, env)
	-- p(env)
	return env
end

---@param desc flex_value
---@param len? integer
---@param elems? flex_value[]
---@return integer len
---@return flex_value[] elems
local function traverse(desc, len, elems)
	len = len or 0
	---@type flex_value[]
	elems = elems or {}
	local constructor, arg = desc:unwrap_enum_value()
	if constructor == terms.DescCons.empty then
		terms.unempty(desc)
		return len, elems
	elseif constructor == terms.DescCons.cons then
		local len = len + 1
		local next_desc
		next_desc, elems[len] = terms.uncons(desc)
		return traverse(next_desc, len, elems)
	else
		error("unknown tuple desc constructor")
	end
end
-- desc is head + (gradually) parts of tail
-- elem expects only parts of tail, need to wrap to handle head
-- head_n and tail_n are the lengths of the head and tail component of desc
local function tuple_desc_elem(desc, elem, head_n, head_names, tail_n, tail_names)
	-- in theory the only placeholder name will be in reference to the last
	-- element of head, which is always lost (and sometimes not even asked for)
	local names = spanned_name_array()
	for _, name in head_names:ipairs() do
		names:append(name)
	end
	names:append(spanned_name("#_", format.span_here()))
	for _, name in tail_names:ipairs() do
		names:append(name)
	end
	local arg_dbg = spanned_name("#tuple-desc-concat", format.span_here())
	-- convert to just tuple of tail
	local tail_args = typed_term_array()
	for i = 1, tail_n do
		-- 2 for closure argument and capture (passed to tuple_elim)
		-- head_n for head
		tail_args:append(typed_term.bound_variable(2 + head_n + i, names[1 + head_n + i]))
	end
	local body = typed_term.tuple_elim(
		names:map(name_array, function(n)
			return n.name
		end),
		names,
		typed_term.bound_variable(2, arg_dbg),
		head_n + tail_n,
		typed_term.application(typed_term.literal(elem), typed_term.tuple_cons(tail_args))
	)
	local elem_wrap = flex_value.closure(
		"#tuple-desc-concat",
		body,
		flex_value.strict(empty_tuple),
		spanned_name("", format.span_here()),
		arg_dbg
	)
	return U.notail(terms.cons(desc, elem_wrap))
end

local function tuple_desc_concat(head, tail)
	local head_n, head_elems = traverse(head)
	local tail_n, tail_elems = traverse(tail)
	---@type flex_value
	local head_last = head_elems[1]
	local _, head_code, _, _ = head_last:unwrap_closure()
	local head_names
	if head_code:is_tuple_elim() then
		_, head_names, _, _, _ = head_code:unwrap_tuple_elim()
	else
		head_names = spanned_name_array()
		for i = 1, head_n do
			head_names[i] = spanned_name("head_unk_" .. tostring(i), format.span_here())
		end
	end
	local desc = head
	for i = tail_n, 1, -1 do
		local tail_n_now = tail_n - i
		---@type flex_value
		local elem = tail_elems[i]
		local _, tail_code, _, _ = elem:unwrap_closure()
		local tail_names
		if tail_code:is_tuple_elim() then
			_, tail_names, _, _, _ = tail_code:unwrap_tuple_elim()
		else
			tail_names = spanned_name_array()
			for i = 1, tail_n do
				tail_names[i] = spanned_name("tail_unk_" .. tostring(i), format.span_here())
			end
		end
		desc = tuple_desc_elem(desc, elem, head_n, head_names, tail_n_now, tail_names)
	end
	return desc
end

---@param desc strict_value
---@return strict_value desc `strict_value.enum_value(terms.DescCons.…, …)`
local function convert_desc(desc)
	local constructor, arg = desc:unwrap_enum_value()
	if constructor == terms.DescCons.empty then
		terms.unempty(desc)
		return desc
	elseif constructor == terms.DescCons.cons then
		local next_desc, type_fun = terms.uncons(desc)
		local convert_next = convert_desc(next_desc)
		local convert_type = flex_value
			.variance_type(
				evaluator.apply_value(
					flex_value.strict(type_fun),
					flex_value.stuck(stuck_value.free(terms.free.unique {})),
					terms.typechecking_context()
				)
			)
			:unwrap_strict()
		local capture_dbg = spanned_name("#capture", format.span_here())
		local convert_type_fun = strict_value.closure(
			"#tuple-prefix",
			typed_term.bound_variable(1, capture_dbg),
			convert_type,
			capture_dbg,
			spanned_name("#tuple-prefix", format.span_here())
		)
		terms.verify_placeholder_lite(convert_type_fun, terms.typechecking_context(), false)
		return U.notail(terms.strict_cons(convert_next, convert_type_fun))
	else
		error "unknown tuple desc constructor"
	end
end

---@param sig strict_value `flex_value.pi`
---@return strict_value param_desc `flex_value.tuple_type`
local function convert_sig(sig)
	if not strict_value.value_check(sig) then
		error("expected strict value, did you forget to wrap? " .. tostring(sig))
	end
	local param_type, _, _, _ = sig:unwrap_pi()
	local param_desc = param_type:unwrap_tuple_type()
	return U.notail(strict_value.tuple_type(convert_desc(param_desc)))
end

local function desc_length(desc, len)
	len = len or 0
	local constructor = desc:unwrap_enum_value()
	if constructor == terms.DescCons.empty then
		terms.unempty(desc)
		return len
	elseif constructor == terms.DescCons.cons then
		local next_desc, _ = terms.uncons(desc)
		return desc_length(next_desc, len + 1)
	else
		error("unknown tuple desc constructor")
	end
end
-- TODO: move to `evaluator.gen_base_operator_aux`?
local function new_host_type_family(unique_id, sig, variance)
	local param_type, _, _, _ = sig:unwrap_pi()
	local param_desc = param_type:unwrap_tuple_type()
	local nparams = desc_length(param_desc)

	local variance_elems = variance:unwrap_tuple_value()
	local variances = {}
	for i, v in variance_elems:ipairs() do
		variances[i] = v:unwrap_host_value()
	end

	local srel = evaluator.IndepTupleRelation(variances)
	evaluator.register_host_srel(unique_id, srel)

	local params = typed_term_array()
	local param_names = spanned_name_array()
	for i = 1, nparams do
		local info = spanned_name("#type-family-A-" .. tostring(i), format.span_here())
		params:append(typed_term.bound_variable(i + 2, info))
		param_names:append(info)
	end
	local info = spanned_name("body", format.span_here())
	local body = typed_term.tuple_elim(
		param_names:map(name_array, function(n)
			return n.name
		end),
		param_names,
		typed_term.bound_variable(2, info),
		nparams,
		typed_term.host_user_defined_type_cons(unique_id, params)
	)
	return U.notail(
		strict_value.closure("#type-family-B", body, empty_tuple, spanned_name("#capture", format.span_here()), info)
	)
end

---@param subject flex_value
---@return flex_value
local function get_host_func_res(subject, valid)
	local param_type, result_type, result_info = subject:unwrap_host_function_type()

	local result_dbg = spanned_name("#result_type", format.span_here())
	local arg_dbg = spanned_name("#res_arg", format.span_here())
	local tuple_build = typed_term.tuple_cons(
		typed_term_array(
			typed_term.host_wrap(
				typed_term.application(typed_term.bound_variable(1, result_dbg), typed_term.bound_variable(2, arg_dbg))
			),
			typed_term.literal(strict_value.host_value(nil))
		)
	)
	return U.notail(strict_value.closure("#TEST-1", tuple_build, result_type, result_dbg, arg_dbg))
end

---@param val strict_value
---@return strict_value
local function tuple_to_host_tuple_inner(_type, _valid, val)
	local elems = val:unwrap_tuple_value()
	local leading = gen.declare_array(gen.any_lua_type)()
	local stuck = false
	local stuck_elem = nil
	local trailing = flex_value_array()
	for _, v in ipairs(elems) do
		---@cast v flex_value
		if stuck then
			trailing:append(v)
		elseif v:is_host_value() then
			leading:append(v:unwrap_host_value())
		elseif v:is_stuck() then
			stuck, stuck_elem = true, v:unwrap_stuck()
		else
			error "found an element in a tuple being converted to host-tuple that was neither host nor neutral"
		end
	end
	if not stuck then
		return U.notail(strict_value.host_tuple_value(leading))
	else
		error("should be unreachable TODO refactor and remove")
		return U.notail(flex_value.stuck(stuck_value.host_tuple(leading, stuck_elem, trailing)))
	end
end

local base_env = {
	ascribed_segment_tuple_desc = ascribed_segment_tuple_desc,
	create = create,
	tuple_desc_concat = tuple_desc_concat,
	convert_sig = convert_sig,
	new_host_type_family = new_host_type_family,
	tuple_to_host_tuple_inner = tuple_to_host_tuple_inner,
	get_host_func_res = get_host_func_res,
	gen_base_operator = gen_base_operator,
}
local internals_interface = require "internals-interface"
internals_interface.base_env = base_env
return base_env
