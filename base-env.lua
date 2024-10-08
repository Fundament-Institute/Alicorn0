local environment = require "environment"
local trie = require "lazy-prefix-tree"
local metalanguage = require "metalanguage"
local utils = require "reducer-utils"
local exprs = require "alicorn-expressions"
local terms = require "terms"
local gen = require "terms-generators"
local evaluator = require "evaluator"

local value = terms.value
local typed = terms.typed_term

local param_info_explicit = value.param_info(value.visibility(terms.visibility.explicit))
local result_info_pure = value.result_info(terms.result_info(terms.purity.pure))
local result_info_effectful = value.result_info(terms.result_info(terms.purity.effectful))

local usage_array = gen.declare_array(gen.builtin_number)

---@param val value
---@param typ value
---@return inferrable
local function lit_term(val, typ)
	return terms.inferrable_term.typed(typ, usage_array(), terms.typed_term.literal(val))
end

--- lua_operative is dependently typed and should produce inferrable vs checkable depending on the goal, and an error as the second return if it failed
--- | unknown in the second return insufficiently constrains the non-error cases to be inferrable or checkable terms
--- this can be fixed in the future if we swap to returning a Result type that can express the success/error constraint separately
---@alias lua_operative fun(syntax : ConstructedSyntax, env : Environment, goal : expression_goal) : boolean, inferrable | checkable | string, Environment?

---handle a let binding
---@type lua_operative
local function let_bind(syntax, env)
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
		error("env in let_bind isn't an env")
	end

	if type(name) == "table" then
		--print("binding destructuring with let")
		--p(name)
		local tupletype = gen.declare_array(gen.builtin_string)
		env = env:bind_local(terms.binding.tuple_elim(tupletype(table.unpack(name)), expr))
	else
		env = env:bind_local(terms.binding.let(name, expr))
	end

	return true,
		terms.inferrable_term.typed(
			terms.unit_type,
			gen.declare_array(gen.builtin_number)(),
			terms.typed_term.literal(terms.unit_val)
		),
		env
end

---@param _ any
---@param name string
---@param exprenv { val:inferrable, env:Environment }
---@return boolean
---@return { name:string, expr:inferrable }
---@return Environment
local function record_threaded_element_acceptor(_, name, exprenv)
	local expr, env = utils.unpack_val_env(exprenv)
	return true, { name = name, expr = expr }, env
end

---@param env Environment
---@return Matcher
local function record_threaded_element(env)
	return metalanguage.listmatch(
		record_threaded_element_acceptor,
		metalanguage.issymbol(metalanguage.accept_handler),
		metalanguage.symbol_exact(metalanguage.accept_handler, "="),
		exprs.inferred_expression(utils.accept_with_env, env)
	)
end

---@type lua_operative
local function record_build(syntax, env)
	local ok, defs, env = syntax:match({
		metalanguage.list_many_fold(metalanguage.accept_handler, record_threaded_element, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, defs
	end
	local map = gen.declare_map(gen.builtin_string, terms.inferrable_term)()
	for _, v in ipairs(defs) do
		map[v.name] = v.expr
	end
	return true, terms.inferrable_term.record_cons(map), env
end

---@type lua_operative
local function intrinsic(syntax, env)
	local ok, str_env, syntax = syntax:match({
		metalanguage.listtail(
			metalanguage.accept_handler,
			exprs.expression(
				utils.accept_with_env,
				exprs.ExpressionArgs.new(terms.expression_goal.check(value.host_string_type), env)
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
		terms.inferrable_term.host_intrinsic(str, type--[[terms.checkable_term.inferrable(type)]], syntax.anchor),
		env
end

local pure_ascribed_name = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return string
	---@return inferrable?
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
			type = terms.inferrable_term.typed(
				value.star(evaluator.OMEGA, 1),
				usage_array(),
				typed.literal(type_mv:as_value())
			)
		end
		return true, name, type, env
	end,
	"pure_ascribed_name"
)

local ascribed_name = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@param prev inferrable
	---@param names string[]
	---@return boolean
	---@return string
	---@return inferrable?
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
		env = env:bind_local(terms.binding.annotated_lambda("#prev", prev, syntax.anchor, terms.visibility.explicit))
		local ok, prev_binding = env:get("#prev")
		if not ok then
			error "#prev should always be bound, was just added"
		end
		---@cast prev_binding -string
		env = env:bind_local(terms.binding.tuple_elim(names, prev_binding))
		local ok, name, val, env =
			syntax:match({ pure_ascribed_name(metalanguage.accept_handler, env) }, metalanguage.failure_handler, nil)
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
				return pure_ascribed_name(function(_, name, type_val, type_env)
					type_env = type_env:bind_local(
						terms.binding.annotated_lambda(name, type_val, syntax.anchor, terms.visibility.implicit)
					)
					local newthread = {
						env = type_env,
					}
					return true, { name = name, type = type_val }, newthread
				end, thread.env)
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

local tupleof_ascribed_names_inner = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: inferrable, env: Environment}|string
	function(syntax, env)
		local function build_type_term(args)
			return terms.inferrable_term.tuple_type(args)
		end
		local inf_array = gen.declare_array(terms.inferrable_term)
		local function tup_cons(...)
			return terms.inferrable_term.tuple_cons(inf_array(...))
		end
		local function cons(...)
			return terms.inferrable_term.enum_cons(
				terms.value.tuple_desc_type(terms.value.star(0, 0)),
				terms.DescCons.cons,
				tup_cons(...)
			)
		end
		local empty = terms.inferrable_term.enum_cons(
			terms.value.tuple_desc_type(terms.value.star(0, 0)),
			terms.DescCons.empty,
			tup_cons()
		)
		local names = gen.declare_array(gen.builtin_string)()

		local ok, thread = syntax:match({
			metalanguage.list_many_fold(function(_, vals, thread)
				return true, thread
			end, function(thread)
				return ascribed_name(function(_, name, type_val, type_env)
					local names = thread.names:copy()
					names:append(name)
					local newthread = {
						names = names,
						args = cons(thread.args, type_val),
						env = type_env,
					}
					return true, { name = name, type = type_val }, newthread
				end, thread.env, build_type_term(thread.args), thread.names)
			end, {
				names = names,
				args = empty,
				env = env,
			}),
		}, metalanguage.failure_handler, nil)

		return ok, thread
	end,
	"tupleof_ascribed_names_inner"
)

local tupleof_ascribed_names = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: inferrable, env: Environment}|string
	function(syntax, env)
		local ok, thread = syntax:match({
			tupleof_ascribed_names_inner(metalanguage.accept_handler, env),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, thread
		end
		thread.args = terms.inferrable_term.tuple_type(thread.args)
		return ok, thread
	end,
	"tupleof_ascribed_names"
)

local host_tupleof_ascribed_names = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: inferrable, env: Environment}|string
	function(syntax, env)
		local ok, thread = syntax:match({
			tupleof_ascribed_names_inner(metalanguage.accept_handler, env),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, thread
		end
		thread.args = terms.inferrable_term.host_tuple_type(thread.args)
		return ok, thread
	end,
	"host_tupleof_ascribed_names"
)

local ascribed_segment = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {single: boolean, names: string|string[], args: inferrable, env: Environment}|string
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
				tupleof_ascribed_names(metalanguage.accept_handler, env),
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
	---@return {single: boolean, names: string|string[], args: inferrable, env: Environment}|string
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
				host_tupleof_ascribed_names(metalanguage.accept_handler, env),
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

local tuplewrap_ascribed_name_inner = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: inferrable, env: Environment}|string
	function(syntax, env)
		local function build_type_term(args)
			return terms.inferrable_term.tuple_type(args)
		end
		local inf_array = gen.declare_array(terms.inferrable_term)
		local function tup_cons(...)
			return terms.inferrable_term.tuple_cons(inf_array(...))
		end
		local function cons(...)
			return terms.inferrable_term.enum_cons(
				terms.value.tuple_desc_type(terms.value.star(0, 0)),
				terms.DescCons.cons,
				tup_cons(...)
			)
		end
		local empty = terms.inferrable_term.enum_cons(
			terms.value.tuple_desc_type(terms.value.star(0, 0)),
			terms.DescCons.empty,
			tup_cons()
		)
		local names = gen.declare_array(gen.builtin_string)()
		local args = empty
		local ok, name, type_val, type_env = syntax:match({
			ascribed_name(metalanguage.accept_handler, env, build_type_term(args), names),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, name
		end

		names = names:copy()
		names:append(name)
		args = cons(args, type_val)
		env = type_env
		return ok, { names = names, args = args, env = env }
	end,
	"tuplewrap_ascribed_name_inner"
)

local tuplewrap_ascribed_name = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: inferrable, env: Environment}|string
	function(syntax, env)
		local ok, thread = syntax:match({
			tuplewrap_ascribed_name_inner(metalanguage.accept_handler, env),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, thread
		end
		thread.args = terms.inferrable_term.tuple_type(thread.args)
		return ok, thread
	end,
	"tuplewrap_ascribed_name"
)

local host_tuplewrap_ascribed_name = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: inferrable, env: Environment}|string
	function(syntax, env)
		local ok, thread = syntax:match({
			tuplewrap_ascribed_name_inner(metalanguage.accept_handler, env),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, thread
		end
		thread.args = terms.inferrable_term.host_tuple_type(thread.args)
		return ok, thread
	end,
	"host_tuplewrap_ascribed_name"
)

local ascribed_segment_2 = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: inferrable, env: Environment}|string
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
				tuplewrap_ascribed_name(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
		else
			ok, thread = syntax:match({
				tupleof_ascribed_names(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
		end

		return ok, thread
	end,
	"ascribed_segment_2"
)

local host_ascribed_segment_2 = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: inferrable, env: Environment}|string
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
				host_tuplewrap_ascribed_name(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
		else
			ok, thread = syntax:match({
				host_tupleof_ascribed_names(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
		end

		return ok, thread
	end,
	"host_ascribed_segment_2"
)

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
		local params_names = params_thread.names
		env = params_thread.env

		--print("moving on to return type")

		local shadowed
		shadowed, env = env:enter_block(terms.block_purity.pure)
		-- tail.anchor can be nil so we fall back to the anchor for the start of this host func type if needed
		-- TODO: use correct name in lambda parameter instead of adding an extra let
		env = env:bind_local(
			terms.binding.annotated_lambda(
				"#host-func-arguments",
				params_args,
				tail.anchor or syntax.anchor,
				terms.visibility.explicit
			)
		)
		local ok, arg = env:get("#host-func-arguments")
		if not ok then
			error("wtf")
		end
		---@cast arg -string
		if params_single then
			env = env:bind_local(terms.binding.let(params_names, arg))
		else
			env = env:bind_local(terms.binding.tuple_elim(params_names, arg))
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
			local effect_description =
				terms.value.effect_row(gen.declare_set(terms.unique_id)(terms.lua_prog), terms.value.effect_empty)
			local effect_term = terms.inferrable_term.typed(
				terms.value.effect_row_type,
				usage_array(),
				terms.typed_term.literal(effect_description)
			)
			results_args = terms.inferrable_term.program_type(effect_term, results_args)
		end

		local env, fn_res_term, purity = env:exit_block(results_args, shadowed)
		local fn_type_term = terms.inferrable_term.host_function_type(
			params_args,
			fn_res_term,
			terms.checkable_term.inferrable(
				terms.inferrable_term.typed(
					terms.value.result_info_type,
					usage_array(),
					terms.typed_term.literal(effectful and result_info_effectful or result_info_pure)
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
local function forall_type_impl(syntax, env)
	if not env or not env.enter_block then
		error "env isn't an environment in forall_type_impl"
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
	local params_names = params_thread.names
	env = params_thread.env

	--print("moving on to return type")

	local shadowed
	shadowed, env = env:enter_block(terms.block_purity.pure)
	-- tail.anchor can be nil so we fall back to the anchor for the start of this forall type if needed
	-- TODO: use correct name in lambda parameter instead of adding an extra let
	env = env:bind_local(
		terms.binding.annotated_lambda(
			"#forall-arguments",
			params_args,
			tail.anchor or syntax.anchor,
			terms.visibility.explicit
		)
	)
	local ok, arg = env:get("#forall-arguments")
	if not ok then
		error("wtf")
	end
	---@cast arg -string
	if params_single then
		env = env:bind_local(terms.binding.let(params_names, arg))
	else
		env = env:bind_local(terms.binding.tuple_elim(params_names, arg))
	end

	local ok, results_thread = tail:match({
		metalanguage.listmatch(metalanguage.accept_handler, ascribed_segment(metalanguage.accept_handler, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, results_thread
	end

	local results_args = results_thread.args
	env = results_thread.env

	local env, fn_res_term, purity = env:exit_block(results_args, shadowed)
	local usage_array = gen.declare_array(gen.builtin_number)
	local fn_type_term = terms.inferrable_term.pi(
		params_args,
		terms.checkable_term.inferrable(
			terms.inferrable_term.typed(
				terms.value.param_info_type,
				usage_array(),
				terms.typed_term.literal(param_info_explicit)
			)
		),
		fn_res_term,
		terms.checkable_term.inferrable(
			terms.inferrable_term.typed(
				terms.value.result_info_type,
				usage_array(),
				terms.typed_term.literal(result_info_pure)
			)
		)
	)

	--print("reached end of function type construction")
	if not env.enter_block then
		error "env isn't an environment at end in forall_type_impl"
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

	local type_of_typed_term, usages, type_typed_term = evaluator.infer(type_inferrable_term, env.typechecking_context)
	local evaled_type = evaluator.evaluate(type_typed_term, env.typechecking_context.runtime_context)

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
	return ok, terms.inferrable_term.annotated(val, type_inferrable_term), env
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

	local type_of_fn, usages, fn_typed_term = evaluator.infer(fn_inferrable_term, env.typechecking_context)

	-- TODO: apply operative?
	-- TODO: param info and result info
	local param_type_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
	--local param_info_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
	local result_type_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
	--local result_info_mv = evaluator.typechecker_state:metavariable(env.typechecking_context)
	local param_type = param_type_mv:as_value()
	--local param_info = param_info_type_mv:as_value()
	local param_info = param_info_explicit
	local result_type = result_type_mv:as_value()
	--local result_info = result_info_type_mv:as_value()
	local result_info = result_info_pure
	local spec_type = value.pi(param_type, param_info, result_type, result_info)
	local host_spec_type = value.host_function_type(param_type, result_type, result_info)

	local function rest_of_apply(spec_type)
		evaluator.typechecker_state:flow(
			type_of_fn,
			env.typechecking_context,
			spec_type,
			env.typechecking_context,
			"apply"
		)

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
		return terms.inferrable_term.application(
			terms.inferrable_term.typed(spec_type, usages, fn_typed_term),
			inf_term
		),
			env
	end

	local ok, res1, res1env, res2, res2env
	ok, res1, res1env = evaluator.typechecker_state:speculate(function()
		return rest_of_apply(spec_type)
	end)
	if ok then
		return true, res1, res1env
	end
	ok, res2, res2env = evaluator.typechecker_state:speculate(function()
		return rest_of_apply(host_spec_type)
	end)
	if ok then
		return true, res2, res2env
	end
	--error(res1)
	--error(res2)
	error("apply() speculation failed! debugging this is left as an exercise to the maintainer")
end

---@type lua_operative
local function lambda_impl(syntax, env)
	local ok, thread, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, ascribed_segment_2(metalanguage.accept_handler, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end

	local args, names, env = thread.args, thread.names, thread.env

	local shadow, inner_env = env:enter_block(terms.block_purity.pure)
	inner_env = inner_env:bind_local(
		terms.binding.annotated_lambda("#lambda-arguments", args, syntax.anchor, terms.visibility.explicit)
	)
	local _, arg = inner_env:get("#lambda-arguments")
	inner_env = inner_env:bind_local(terms.binding.tuple_elim(names, arg))
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

	local name, arg, env = table.unpack(thread)

	local shadow, inner_env = env:enter_block(terms.block_purity.pure)
	inner_env =
		inner_env:bind_local(terms.binding.annotated_lambda(name, arg, syntax.anchor, terms.visibility.explicit))
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
local function lambda_implicit_impl(syntax, env)
	local ok, thread, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, pure_ascribed_name(utils.accept_bundled, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end

	local name, arg, env = table.unpack(thread)

	local shadow, inner_env = env:enter_block(terms.block_purity.pure)
	inner_env =
		inner_env:bind_local(terms.binding.annotated_lambda(name, arg, syntax.anchor, terms.visibility.implicit))
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
	local term = terms.inferrable_term.typed(
		value.star(level_val.val + 1, depth_val.val + 1),
		usage_array(),
		terms.typed_term.star(level_val.val, depth_val.val)
	)

	return true, term, env
end

---@param goal goal
---@return value
local function host_term_of_inner(goal)
	if goal:is_infer() then
		return terms.host_inferrable_term_type
	elseif goal:is_check() then
		return terms.host_checkable_term_type
	else
		error("host_term_of_inner: unknown goal")
	end
end
local host_term_of_inner_type = value.host_function_type(
	value.host_tuple_type(
		terms.tuple_desc(value.closure("#htoit-empty", typed.literal(terms.host_goal_type), terms.runtime_context()))
	),
	value.closure(
		"#htoit-params",
		typed.literal(
			value.host_tuple_type(
				terms.tuple_desc(
					value.closure(
						"#htoit-empty",
						typed.host_wrapped_type(typed.literal(value.host_type_type)),
						terms.runtime_context()
					)
				)
			)
		),
		terms.runtime_context()
	),
	result_info_pure
)

---@param goal typed
---@param context_len integer
---@return typed
local function host_term_of(goal, context_len)
	local teees = gen.declare_array(typed)
	local names = gen.declare_array(gen.builtin_string)
	local t = names("#host_term_of-t")
	return typed.tuple_elim(
		t,
		typed.application(typed.literal(value.host_value(host_term_of_inner)), typed.host_tuple_cons(teees(goal))),
		1,
		typed.host_unwrap(typed.bound_variable(context_len + 1))
	)
end

---@param ud_type value
---@return value
local function operative_handler_type(ud_type)
	local teees = gen.declare_array(typed)
	local names = gen.declare_array(gen.builtin_string)
	local namesp4 = names(
		"#operative_handler_type-syn",
		"#operative_handler_type-env",
		"#operative_handler_type-ud",
		"#operative_handler_type-goal"
	)
	local pnamep0 = "#operative_handler_type-empty"
	local pnamep1 = "#operative_handler_type-syn"
	local pnamep2 = "#operative_handler_type-syn-env"
	local pnamep3 = "#operative_handler_type-syn-env-ud"
	local pnamer = "#operative_handler_type-params"
	local pnamer0 = "#operative_handler_type-result-empty"
	local pnamer1 = "#operative_handler_type-result-term"
	return value.pi(
		value.tuple_type(
			terms.tuple_desc(
				value.closure(pnamep0, typed.literal(terms.host_syntax_type), terms.runtime_context()),
				value.closure(pnamep1, typed.literal(terms.host_environment_type), terms.runtime_context()),
				value.closure(pnamep2, typed.literal(ud_type), terms.runtime_context()),
				value.closure(pnamep3, typed.literal(terms.host_goal_type), terms.runtime_context())
			)
		),
		param_info_explicit,
		value.closure(
			pnamer,
			typed.tuple_elim(
				namesp4,
				typed.bound_variable(1),
				4,
				typed.tuple_type(
					typed.enum_cons(
						terms.DescCons.cons,
						typed.tuple_cons(
							teees(
								typed.enum_cons(
									terms.DescCons.cons,
									typed.tuple_cons(
										teees(
											typed.enum_cons(terms.DescCons.empty, typed.tuple_cons(teees())),
											typed.lambda(pnamer0, host_term_of(typed.bound_variable(5), 6))
										)
									)
								),
								typed.lambda(pnamer1, typed.literal(terms.host_environment_type))
							)
						)
					)
				)
			),
			terms.runtime_context()
		),
		result_info_pure
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
	}, metalanguage.failure_handler)
	if not ok then
		return false, ud_type_syntax
	end

	local ok, ud_type_chk, env = ud_type_syntax:match({
		exprs.expression(
			metalanguage.accept_handler,
			exprs.ExpressionArgs.new(terms.expression_goal.check(value.host_type_type), env)
		),
	}, metalanguage.failure_handler)
	if not ok then
		return false, ud_type_chk
	end
	local ud_type_usages, ud_type_t = evaluator.check(ud_type_chk, env.typechecking_context, value.host_type_type)
	local ud_type = evaluator.evaluate(ud_type_t, env.typechecking_context.runtime_context)

	local ok, ud_chk, env = ud_syntax:match({
		exprs.expression(
			metalanguage.accept_handler,
			exprs.ExpressionArgs.new(terms.expression_goal.check(ud_type), env)
		),
	}, metalanguage.failure_handler)
	if not ok then
		return false, ud_chk
	end
	local ud_usages, ud_t = evaluator.check(ud_chk, env.typechecking_context, ud_type)
	local ud = evaluator.evaluate(ud_t, env.typechecking_context.runtime_context)

	local ok, handler_chk, env = handler_syntax:match({
		exprs.expression(
			metalanguage.accept_handler,
			exprs.ExpressionArgs.new(terms.expression_goal.check(operative_handler_type(ud_type)), env)
		),
	}, metalanguage.failure_handler)
	if not ok then
		return false, handler_chk
	end
	local handler_usages, handler_t =
		evaluator.check(handler_chk, env.typechecking_context, operative_handler_type(ud_type))
	local handler = evaluator.evaluate(handler_t, env.typechecking_context.runtime_context)

	local op_type = value.operative_type(handler, ud_type)
	local op_val = value.operative_value(ud)

	return true, terms.inferrable_term.typed(op_type, usage_array(), typed.literal(op_val)), env
end

-- eg typed.host_wrap, typed.host_wrapped_type
---@param body_fn fun(typed): typed
---@param type_fn fun(typed): typed
---@return inferrable
local function build_wrap(body_fn, type_fn)
	local names = gen.declare_array(gen.builtin_string)
	local names0 = names()
	local names1 = names("#wrap-TODO1")
	local names2 = names("#wrap-TODO1", "#wrap-TODO2")
	local pname_arg = "#wrap-arguments"
	local pname_type = "#wrap-prev"
	return lit_term(
		value.closure(
			pname_arg,
			typed.tuple_elim(names2, typed.bound_variable(1), 2, body_fn(typed.bound_variable(3))),
			terms.runtime_context()
		),
		value.pi(
			value.tuple_type(
				terms.tuple_desc(
					value.closure(
						pname_type,
						typed.tuple_elim(names0, typed.bound_variable(1), 0, typed.star(evaluator.OMEGA + 1, 0)),
						terms.runtime_context()
					),
					value.closure(
						pname_type,
						terms.typed_term.tuple_elim(
							names1,
							terms.typed_term.bound_variable(1),
							1,
							typed.bound_variable(2)
						),
						terms.runtime_context()
					)
				)
			),
			param_info_explicit,
			value.closure(
				pname_type,
				typed.tuple_elim(names2, typed.bound_variable(1), 2, type_fn(typed.bound_variable(2))),
				terms.runtime_context()
			),
			result_info_pure
		)
	)
end

-- eg typed.host_unwrap, typed.host_wrapped_type
---@param body_fn fun(typed): typed
---@param type_fn fun(typed): typed
---@return inferrable
local function build_unwrap(body_fn, type_fn)
	local names = gen.declare_array(gen.builtin_string)
	local names0 = names()
	local names1 = names("#unwrap-TODO1")
	local names2 = names("#unwrap-TODO1", "#unwrap-TODO2")
	local pname_arg = "#unwrap-arguments"
	local pname_type = "#unwrap-prev"
	return lit_term(
		value.closure(
			pname_arg,
			typed.tuple_elim(names2, typed.bound_variable(1), 2, body_fn(typed.bound_variable(3))),
			terms.runtime_context()
		),
		value.pi(
			value.tuple_type(
				terms.tuple_desc(
					value.closure(
						pname_type,
						typed.tuple_elim(names0, typed.bound_variable(1), 0, typed.star(evaluator.OMEGA + 1, 0)),
						terms.runtime_context()
					),
					value.closure(
						pname_type,
						terms.typed_term.tuple_elim(
							names1,
							terms.typed_term.bound_variable(1),
							1,
							type_fn(typed.bound_variable(2))
						),
						terms.runtime_context()
					)
				)
			),
			param_info_explicit,
			value.closure(
				pname_type,
				typed.tuple_elim(names2, typed.bound_variable(1), 2, typed.bound_variable(2)),
				terms.runtime_context()
			),
			result_info_pure
		)
	)
end

-- eg typed.host_wrapped_type,
---@param body_fn fun(typed): typed
---@return inferrable
local function build_wrapped(body_fn)
	local names = gen.declare_array(gen.builtin_string)
	local names0 = names()
	local names1 = names("#wrapped-TODO1")
	local pname_arg = "#wrapped-arguments"
	local pname_type = "#wrapped-prev"
	return lit_term(
		value.closure(
			pname_arg,
			typed.tuple_elim(names1, typed.bound_variable(1), 1, body_fn(typed.bound_variable(2))),
			terms.runtime_context()
		),
		value.pi(
			value.tuple_type(
				terms.tuple_desc(
					value.closure(
						pname_type,
						typed.tuple_elim(names0, typed.bound_variable(1), 0, typed.star(evaluator.OMEGA + 1, 0)),
						terms.runtime_context()
					)
				)
			),
			param_info_explicit,
			value.closure(
				pname_type,
				typed.tuple_elim(names1, typed.bound_variable(1), 1, typed.literal(value.host_type_type)),
				terms.runtime_context()
			),
			result_info_pure
		)
	)
end

local core_operations = {
	["+"] = exprs.host_applicative(function(a, b)
		return a + b
	end, { value.host_number_type, value.host_number_type }, { value.host_number_type }),
	["-"] = exprs.host_applicative(function(a, b)
		return a - b
	end, { value.host_number_type, value.host_number_type }, { value.host_number_type }),
	["*"] = exprs.host_applicative(function(a, b)
		return a * b
	end, { value.host_number_type, value.host_number_type }, { value.host_number_type }),
	["/"] = exprs.host_applicative(function(a, b)
		return a / b
	end, { value.host_number_type, value.host_number_type }, { value.host_number_type }),
	["%"] = exprs.host_applicative(function(a, b)
		return a % b
	end, { value.host_number_type, value.host_number_type }, { value.host_number_type }),
	neg = exprs.host_applicative(function(a)
		return -a
	end, { value.host_number_type }, { value.host_number_type }),

	--["<"] = evaluator.host_applicative(function(args)
	--  return { variant = (args[1] < args[2]) and 1 or 0, arg = types.unit_val }
	--end, types.tuple {types.number, types.number}, types.cotuple({types.unit, types.unit})),
	--["=="] = evaluator.host_applicative(function(args)
	--  return { variant = (args[1] == args[2]) and 1 or 0, arg = types.unit_val }
	--end, types.tuple {types.number, types.number}, types.cotuple({types.unit, types.unit})),

	--["do"] = evaluator.host_operative(do_block),
	let = exprs.host_operative(let_bind, "let_bind"),
	record = exprs.host_operative(record_build, "record_build"),
	intrinsic = exprs.host_operative(intrinsic, "intrinsic"),
	["host-number"] = lit_term(value.host_number_type, value.host_type_type),
	["host-type"] = lit_term(value.host_type_type, value.star(1, 1)),
	["host-func-type"] = exprs.host_operative(make_host_func_syntax(false), "host_func_type_impl"),
	["host-prog-type"] = exprs.host_operative(make_host_func_syntax(true), "host_prog_type_impl"),
	type = lit_term(value.star(0, 0), value.star(1, 1)),
	type_ = exprs.host_operative(startype_impl, "startype_impl"),
	["forall"] = exprs.host_operative(forall_type_impl, "forall_type_impl"),
	lambda = exprs.host_operative(lambda_impl, "lambda_impl"),
	lambda_single = exprs.host_operative(lambda_single_impl, "lambda_single_impl"),
	lambda_implicit = exprs.host_operative(lambda_implicit_impl, "lambda_implicit_impl"),
	lambda_curry = exprs.host_operative(lambda_curry_impl, "lambda_curry_impl"),
	the = exprs.host_operative(the_operative_impl, "the"),
	apply = exprs.host_operative(apply_operative_impl, "apply"),
	wrap = build_wrap(typed.host_wrap, typed.host_wrapped_type),
	["unstrict-wrap"] = build_wrap(typed.host_unstrict_wrap, typed.host_unstrict_wrapped_type),
	wrapped = build_wrapped(typed.host_wrapped_type),
	["unstrict-wrapped"] = build_wrapped(typed.host_unstrict_wrapped_type),
	unwrap = build_unwrap(typed.host_unwrap, typed.host_wrapped_type),
	["unstrict-unwrap"] = build_unwrap(typed.host_unstrict_unwrap, typed.host_unstrict_wrapped_type),
	--["dump-env"] = evaluator.host_operative(function(syntax, env) print(environment.dump_env(env)); return true, types.unit_val, env end),
	--["basic-fn"] = evaluator.host_operative(basic_fn),
	--tuple = evaluator.host_operative(tuple_type_impl),
	--["tuple-of"] = evaluator.host_operative(tuple_of_impl),
	--number = { type = types.type, val = types.number }
	["into-operative"] = exprs.host_operative(into_operative_impl, "into_operative_impl"),
	["hackhack-host-term-of-inner"] = terms.inferrable_term.typed(
		host_term_of_inner_type,
		usage_array(),
		typed.literal(value.host_value(host_term_of_inner))
	),
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

local base_env = {
	tupleof_ascribed_names_inner = tupleof_ascribed_names_inner,
	create = create,
}
local internals_interface = require "internals-interface"
internals_interface.base_env = base_env
return base_env
