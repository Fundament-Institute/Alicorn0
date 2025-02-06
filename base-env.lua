local environment = require "environment"
local trie = require "lazy-prefix-tree"
local metalanguage = require "metalanguage"
local utils = require "reducer-utils"
local exprs = require "alicorn-expressions"
local terms = require "terms"
local gen = require "terms-generators"
local evaluator = require "evaluator"
local U = require "alicorn-utils"

local flex_value = terms.flex_value
local strict_value = terms.strict_value
local typed = terms.typed_term
local var_debug = terms.var_debug

local param_info_explicit = strict_value.param_info(strict_value.visibility(terms.visibility.explicit))
local result_info_pure = strict_value.result_info(terms.result_info(terms.purity.pure))
local result_info_effectful = strict_value.result_info(terms.result_info(terms.purity.effectful))

local usage_array = gen.declare_array(gen.builtin_number)
local debug_array = gen.declare_array(var_debug)
local name_array = gen.declare_array(gen.builtin_string)
local typed_array = gen.declare_array(typed)
local flex_value_array = gen.declare_array(flex_value)

---@param val strict_value
---@param typ strict_value
---@return inferrable
local function lit_term(val, typ)
	return terms.inferrable_term.typed(terms.typed_term.literal(typ), usage_array(), terms.typed_term.literal(val))
end

--- lua_operative is dependently typed and should produce inferrable vs checkable depending on the goal, and an error as the second return if it failed
--- | unknown in the second return insufficiently constrains the non-error cases to be inferrable or checkable terms
--- this can be fixed in the future if we swap to returning a Result type that can express the success/error constraint separately
---@alias lua_operative fun(syntax : ConstructedSyntax, env : Environment, goal : expression_goal) : boolean, inferrable | checkable | string, Environment?

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
		local debugs = debug_array()
		for _, v in ipairs(name) do
			debugs:append(terms.var_debug(v.str, v.start_anchor))
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
		ok, env = env:bind_local(terms.binding.let(name.str, terms.var_debug(name.str, name.start_anchor), expr))
		if not ok then
			return false, env
		end
	end

	return true,
		terms.inferrable_term.typed(
			terms.typed_term.literal(terms.unit_type),
			gen.declare_array(gen.builtin_number)(),
			terms.typed_term.literal(terms.unit_val)
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
	return ok, terms.inferrable_term.enum_cons(name.str, tuple), env
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

---@param ... SyntaxSymbol
---@return ...
local function unwrap_into_string(...)
	local args = table.pack(...)
	for i = 1, args.n do
		args[i] = args[i].str
	end
	return table.unpack(args, 1, args.n)
end

---@param env Environment
local switch_case = metalanguage.reducer(function(syntax, env)
	local ok, tag, tail = syntax:match({ switch_case_header_matcher }, metalanguage.failure_handler, nil)
	if not ok then
		return ok, tag
	end

	local names = gen.declare_array(gen.builtin_string)(unwrap_into_string(table.unpack(tag, 2)))
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
	--TODO rewrite this to use an environment-splitting operation
	env = environment.new_env(env, {
		typechecking_context = env.typechecking_context:append(
			"#switch-subj",
			evaluator.typechecker_state:metavariable(env.typechecking_context):as_flex(),
			nil,
			var_debug("#switch-subj", syntax.start_anchor)
		),
	})
	local shadowed, term
	shadowed, env = env:enter_block(terms.block_purity.inherit)
	ok, env = env:bind_local(terms.binding.tuple_elim(
		names,
		names:map(debug_array, function(n)
			return var_debug(n, U.anchor_here())
		end),
		terms.inferrable_term.bound_variable(env.typechecking_context:len(), terms.var_debug("", U.anchor_here()))
	))
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
	term.start_anchor = syntax.start_anchor --TODO figure out where to store/retrieve the anchors correctly
	term.end_anchor = syntax.end_anchor
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
	local variants = gen.declare_map(gen.builtin_string, terms.inferrable_term)()
	local variant_debug = gen.declare_map(gen.builtin_string, var_debug)()
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
		variant_debug:set(tag.str, var_debug(tag.str, tag.start_anchor))
	end
	return true, terms.inferrable_term.enum_case(subj, variants, variant_debug), env
end

---@param _ any
---@param symbol SyntaxSymbol
---@param exprenv { val:inferrable, env:Environment }
---@return boolean
---@return { name:string, expr:inferrable }
---@return Environment
local function record_threaded_element_acceptor(_, symbol, exprenv)
	local expr, env = utils.unpack_val_env(exprenv)
	return true, { name = symbol.str, expr = expr }, env
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
local function intrinsic_impl(syntax, env)
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
		terms.inferrable_term.host_intrinsic(str, type--[[terms.checkable_term.inferrable(type)]], syntax.start_anchor),
		env
end

---make a checkable term of a specific literal purity
---@param purity purity
---@return checkable
local function make_literal_purity(purity)
	return terms.checkable_term.inferrable(
		terms.inferrable_term.typed(
			typed.literal(terms.host_purity_type),
			usage_array(),
			terms.typed_term.literal(terms.strict_value.host_value(purity))
		)
	)
end
local literal_purity_pure = make_literal_purity(terms.purity.pure)
local literal_purity_effectful = make_literal_purity(terms.purity.effectful)

local pure_ascribed_name = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return var_debug
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
				terms.typed_term.literal(strict_value.star(evaluator.OMEGA, 1)),
				usage_array(),
				typed.metavariable(type_mv)
			)
		end
		return true, var_debug(name.str, name.start_anchor), type, env
	end,
	"pure_ascribed_name"
)

local ascribed_name = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@param prev inferrable
	---@param names var_debug[]
	---@return boolean
	---@return var_debug
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
		local prev_name = "#prev - " .. tostring(syntax.start_anchor)
		local ok
		ok, env = env:bind_local(
			terms.binding.annotated_lambda(
				prev_name,
				prev,
				syntax.start_anchor,
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
		ok, env = env:bind_local(terms.binding.tuple_elim(
			names:map(name_array, function(n)
				return n.name
			end),
			names,
			prev_binding
		))
		if not ok then
			return false, env
		end
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
					local ok
					local str, anchor = name:unwrap_var_debug()
					ok, type_env = type_env:bind_local(
						terms.binding.annotated_lambda(
							str,
							type_val,
							anchor,
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

local tuple_desc_of_ascribed_names = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: var_debug[], args: inferrable, env: Environment}|string
	function(syntax, env)
		local function build_type_term(args)
			return terms.inferrable_term.tuple_type(args)
		end
		local inf_array = gen.declare_array(terms.inferrable_term)
		local function tup_cons(...)
			local args = inf_array(...)
			return terms.inferrable_term.tuple_cons(
				args,
				args:map(debug_array, function(_)
					return var_debug("", U.anchor_here())
				end)
			)
		end
		local function cons(...)
			return terms.inferrable_term.enum_cons(terms.DescCons.cons, tup_cons(...))
		end
		local empty = terms.inferrable_term.enum_cons(terms.DescCons.empty, tup_cons())
		local names = gen.declare_array(var_debug)()

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
	"tuple_desc_of_ascribed_names"
)

local tuple_of_ascribed_names = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: inferrable, env: Environment}|string
	function(syntax, env)
		local ok, thread = syntax:match({
			tuple_desc_of_ascribed_names(metalanguage.accept_handler, env),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, thread
		end
		thread.args = terms.inferrable_term.tuple_type(thread.args)
		return ok, thread
	end,
	"tuple_of_ascribed_names"
)

local host_tuple_of_ascribed_names = metalanguage.reducer(
	---@param syntax ConstructedSyntax
	---@param env Environment
	---@return boolean
	---@return {names: string[], args: inferrable, env: Environment}|string
	function(syntax, env)
		local ok, thread = syntax:match({
			tuple_desc_of_ascribed_names(metalanguage.accept_handler, env),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, thread
		end
		thread.args = terms.inferrable_term.host_tuple_type(thread.args)
		return ok, thread
	end,
	"host_tuple_of_ascribed_names"
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
	---@return {names: string[], args: inferrable, env: Environment}|string
	function(syntax, env)
		local function build_type_term(args)
			return terms.inferrable_term.tuple_type(args)
		end
		local inf_array = gen.declare_array(terms.inferrable_term)
		local function tup_cons(...)
			local args = inf_array(...)
			return terms.inferrable_term.tuple_cons(
				args,
				args:map(debug_array, function(_)
					return var_debug("", U.anchor_here())
				end)
			)
		end
		local function cons(...)
			return terms.inferrable_term.enum_cons(terms.DescCons.cons, tup_cons(...))
		end
		local empty = terms.inferrable_term.enum_cons(terms.DescCons.empty, tup_cons())
		local names = gen.declare_array(var_debug)()
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
	"tuple_desc_wrap_ascribed_name"
)

local ascribed_segment_tuple_desc = metalanguage.reducer(
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
	local ok, thread = syntax:match({
		ascribed_segment_tuple_desc(metalanguage.accept_handler, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end
	thread.args = terms.inferrable_term.tuple_type(thread.args)
	return ok, thread
end, "ascribed_segment_tuple")

local host_ascribed_segment_tuple = metalanguage.reducer(function(syntax, env)
	local ok, thread = syntax:match({
		ascribed_segment_tuple_desc(metalanguage.accept_handler, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, thread
	end
	thread.args = terms.inferrable_term.host_tuple_type(thread.args)
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
		ok, env = env:bind_local(
			terms.binding.annotated_lambda(
				"#host-func-arguments",
				params_args,
				tail.start_anchor or syntax.start_anchor,
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
			local effect_description = terms.strict_value.effect_row(gen.declare_set(terms.unique_id)(terms.lua_prog))
			local effect_term = terms.inferrable_term.typed(
				terms.typed_term.literal(terms.strict_value.effect_row_type),
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
					terms.typed_term.literal(terms.strict_value.result_info_type),
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

	ok, env = env:bind_local(
		terms.binding.annotated_lambda(
			inner_name,
			params_args,
			tail.start_anchor or syntax.start_anchor,
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

	local usage_array = gen.declare_array(gen.builtin_number)
	local fn_type_term = terms.inferrable_term.pi(
		params_args,
		terms.checkable_term.inferrable(
			terms.inferrable_term.typed(
				terms.typed_term.literal(terms.strict_value.param_info_type),
				usage_array(),
				terms.typed_term.literal(param_info_explicit)
			)
		),
		fn_res_term,
		terms.checkable_term.inferrable(
			terms.inferrable_term.typed(
				terms.typed_term.literal(terms.strict_value.result_info_type),
				usage_array(),
				terms.typed_term.literal(result_info_pure)
			)
		)
	)
	fn_type_term.original_name = inner_name
	params_args.original_name = "param_type for " .. fn_type_term.original_name
	fn_res_term.original_name = "result_type for " .. fn_type_term.original_name

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
	local param_info = param_info_explicit
	local result_type = result_type_mv:as_flex()
	--local result_info = result_info_type_mv:as_flex()
	local result_info = result_info_pure
	local spec_type = flex_value.pi(param_type, param_info, result_type, result_info)
	local host_spec_type = flex_value.host_function_type(param_type, result_type, result_info)

	local function apply_inner(spec_type)
		local ok, err = evaluator.typechecker_state:speculate(function()
			return evaluator.typechecker_state:flow(
				type_of_fn,
				env.typechecking_context,
				spec_type,
				env.typechecking_context,
				terms.constraintcause.primitive("apply", U.anchor_here())
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
			terms.inferrable_term.application(
				terms.inferrable_term.typed(
					evaluator.substitute_placeholders_identity(spec_type, env.typechecking_context),
					usages,
					fn_typed_term
				),
				inf_term
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
			syntax.start_anchor,
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
			syntax.start_anchor,
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
			syntax.start_anchor,
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
			syntax.start_anchor,
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
	evaluator.verify_placeholder_lite(term, resenv.typechecking_context) --DEBUG: check if a placeholder is leaking. remove after tests pass
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
			syntax.start_anchor,
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
	expr = terms.inferrable_term.annotated(terms.checkable_term.inferrable(expr), ann_expr)
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
		terms.typed_term.literal(strict_value.star(level_val.val + 1, depth_val.val + 1)),
		usage_array(),
		terms.typed_term.star(level_val.val, depth_val.val)
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
				typed.literal(terms.host_goal_type),
				terms.strict_runtime_context(),
				terms.var_debug("", U.anchor_here())
			)
		)
	),
	strict_value.closure(
		"#htoit-params",
		typed.literal(
			strict_value.host_tuple_type(
				terms.strict_tuple_desc(
					strict_value.closure(
						"#htoit-empty",
						typed.host_wrapped_type(typed.literal(strict_value.host_type_type)),
						terms.strict_runtime_context(),
						terms.var_debug("", U.anchor_here())
					)
				)
			)
		),
		terms.strict_runtime_context(),
		terms.var_debug("", U.anchor_here())
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
		t:map(debug_array, function(n)
			return var_debug(n, U.anchor_here())
		end),
		typed.application(
			typed.literal(strict_value.host_value(host_term_of_inner)),
			typed.host_tuple_cons(teees(goal))
		),
		1,
		typed.host_unwrap(typed.bound_variable(context_len + 1, terms.var_debug("", U.anchor_here())))
	)
end

---@param ud_type strict_value
---@param anchor Anchor
---@return strict_value
local function operative_handler_type(ud_type, anchor)
	local teees = gen.declare_array(typed)
	local names = gen.declare_array(gen.builtin_string)
	local namesp4 = names(
		terms.var_debug("#operative_handler_type-syn", anchor),
		terms.var_debug("#operative_handler_type-env", anchor),
		terms.var_debug("#operative_handler_type-ud", anchor),
		terms.var_debug("#operative_handler_type-goal", anchor)
	)
	local pnamep0 = terms.var_debug("#operative_handler_type-empty", anchor)
	local pnamep1 = terms.var_debug("#operative_handler_type-syn", anchor)
	local pnamep2 = terms.var_debug("#operative_handler_type-syn-env", anchor)
	local pnamep3 = terms.var_debug("#operative_handler_type-syn-env-ud", anchor)
	local pnamer = terms.var_debug("#operative_handler_type-params", anchor)
	local pnamer0 = terms.var_debug("#operative_handler_type-result-empty", anchor)
	local pnamer1 = terms.var_debug("#operative_handler_type-result-term", anchor)
	return strict_value.pi(
		strict_value.tuple_type(
			terms.strict_tuple_desc(
				strict_value.closure(
					pnamep0.name,
					typed.literal(terms.host_syntax_type),
					terms.strict_runtime_context(),
					pnamep0
				),
				strict_value.closure(
					pnamep1.name,
					typed.literal(terms.host_environment_type),
					terms.strict_runtime_context(),
					pnamep1
				),
				strict_value.closure(pnamep2.name, typed.literal(ud_type), terms.strict_runtime_context(), pnamep2),
				strict_value.closure(
					pnamep3.name,
					typed.literal(terms.host_goal_type),
					terms.strict_runtime_context(),
					pnamep3
				)
			)
		),
		param_info_explicit,
		strict_value.closure(
			pnamer.name,
			typed.tuple_elim(
				namesp4:map(name_array, function(d)
					return d.name
				end),
				namesp4,
				typed.bound_variable(1, pnamer),
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
											typed.lambda(
												pnamer0.name,
												pnamer0,
												host_term_of(typed.bound_variable(5, pnamer0), 6),
												anchor
											)
										)
									)
								),
								typed.lambda(pnamer1.name, pnamer1, typed.literal(terms.host_environment_type), anchor)
							)
						)
					)
				)
			),
			terms.strict_runtime_context(),
			pnamer
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
				terms.expression_goal.check(operative_handler_type(ud_type, syntax.start_anchor)),
				env
			)
		),
	}, metalanguage.failure_handler)
	if not ok then
		return false, handler_chk
	end
	local ok, handler_usages, handler_t =
		evaluator.check(handler_chk, env.typechecking_context, operative_handler_type(ud_type, syntax.start_anchor))
	if not ok then
		return false, handler_usages
	end
	local handler = evaluator.evaluate(handler_t, env.typechecking_context.runtime_context, env.typechecking_context)

	local op_type = flex_value.operative_type(handler, ud_type)
	local op_val = flex_value.operative_value(ud)

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
	local args_dbg = terms.var_debug("#args", U.anchor_here())
	local args0_dbg = terms.var_debug("#args0", U.anchor_here())
	local args1_dbg = terms.var_debug("#args1", U.anchor_here())
	local univ_dbg = terms.var_debug("#univ", U.anchor_here())
	local subj_dbg = terms.var_debug("#subj", U.anchor_here())
	return lit_term(
		strict_value.closure(
			pname_arg,
			typed.tuple_elim(
				names2,
				debug_array(univ_dbg, subj_dbg),
				typed.bound_variable(1, args_dbg),
				2,
				body_fn(typed.bound_variable(3, subj_dbg))
			),
			terms.strict_runtime_context(),
			args_dbg
		),
		strict_value.pi(
			strict_value.tuple_type(
				terms.strict_tuple_desc(
					strict_value.closure(
						pname_type,
						typed.tuple_elim(
							names0,
							debug_array(),
							typed.bound_variable(1, args0_dbg),
							0,
							typed.star(evaluator.OMEGA + 1, 0)
						),
						terms.strict_runtime_context(),
						args0_dbg
					),
					strict_value.closure(
						pname_type,
						terms.typed_term.tuple_elim(
							names1,
							debug_array(univ_dbg),
							terms.typed_term.bound_variable(1, args1_dbg),
							1,
							typed.bound_variable(2, univ_dbg)
						),
						terms.strict_runtime_context(),
						args1_dbg
					)
				)
			),
			param_info_explicit,
			strict_value.closure(
				pname_type,
				typed.tuple_elim(
					names2,
					debug_array(univ_dbg, subj_dbg),
					typed.bound_variable(1, args_dbg),
					2,
					type_fn(typed.bound_variable(2, univ_dbg))
				),
				terms.strict_runtime_context(),
				args_dbg
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
	local args_dbg = terms.var_debug("#args", U.anchor_here())
	local args0_dbg = terms.var_debug("#args0", U.anchor_here())
	local args1_dbg = terms.var_debug("#args1", U.anchor_here())
	local univ_dbg = terms.var_debug("#univ", U.anchor_here())
	local subj_dbg = terms.var_debug("#subj", U.anchor_here())
	return lit_term(
		strict_value.closure(
			pname_arg,
			typed.tuple_elim(
				names2,
				debug_array(univ_dbg, subj_dbg),
				typed.bound_variable(1, args_dbg),
				2,
				body_fn(typed.bound_variable(3, subj_dbg))
			),
			terms.strict_runtime_context(),
			args_dbg
		),
		strict_value.pi(
			strict_value.tuple_type(
				terms.strict_tuple_desc(
					strict_value.closure(
						pname_type,
						typed.tuple_elim(
							names0,
							debug_array(),
							typed.bound_variable(1, args0_dbg),
							0,
							typed.star(evaluator.OMEGA + 1, 0)
						),
						terms.strict_runtime_context(),
						args0_dbg
					),
					strict_value.closure(
						pname_type,
						terms.typed_term.tuple_elim(
							names1,
							debug_array(univ_dbg),
							terms.typed_term.bound_variable(1, args1_dbg),
							1,
							type_fn(typed.bound_variable(2, univ_dbg))
						),
						terms.strict_runtime_context(),
						args1_dbg
					)
				)
			),
			param_info_explicit,
			strict_value.closure(
				pname_type,
				typed.tuple_elim(
					names2,
					debug_array(univ_dbg, subj_dbg),
					typed.bound_variable(1, args_dbg),
					2,
					typed.bound_variable(2, univ_dbg)
				),
				terms.strict_runtime_context(),
				args_dbg
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
	local args_dbg = terms.var_debug("#args", U.anchor_here())
	local args0_dbg = terms.var_debug("#args0", U.anchor_here())
	local typ_dbg = terms.var_debug("#typ", U.anchor_here())
	return lit_term(
		strict_value.closure(
			pname_arg,
			typed.tuple_elim(
				names1,
				debug_array(typ_dbg),
				typed.bound_variable(1, args_dbg),
				1,
				body_fn(typed.bound_variable(2, typ_dbg))
			),
			terms.strict_runtime_context(),
			args_dbg
		),
		strict_value.pi(
			strict_value.tuple_type(
				terms.strict_tuple_desc(
					strict_value.closure(
						pname_type,
						typed.tuple_elim(
							names0,
							debug_array(),
							typed.bound_variable(1, args0_dbg),
							0,
							typed.star(evaluator.OMEGA + 1, 0)
						),
						terms.strict_runtime_context(),
						args0_dbg
					)
				)
			),
			param_info_explicit,
			strict_value.closure(
				pname_type,
				typed.tuple_elim(
					names1,
					debug_array(typ_dbg),
					typed.bound_variable(1, args_dbg),
					1,
					typed.literal(strict_value.host_type_type)
				),
				terms.strict_runtime_context(),
				args_dbg
			),
			result_info_pure
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

	return true, tag.name, terms.inferrable_term.tuple_type(tail.args), env
end, "enum_variant")

---@type lua_operative
local function enum_impl(syntax, env)
	local variants = gen.declare_map(gen.builtin_string, terms.inferrable_term)()
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
		terms.inferrable_term.enum_type(
			terms.inferrable_term.enum_desc_cons(
				variants,
				terms.inferrable_term.typed(
					terms.typed_term.literal(strict_value.enum_desc_type(strict_value.star(0, 0))),
					usage_array(),
					typed.literal(strict_value.enum_desc_value(gen.declare_map(gen.builtin_string, terms.flex_value)()))
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

	term.track = true
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

local core_operations = {
	["+"] = exprs.host_applicative(function(a, b)
		return a + b
	end, { strict_value.host_number_type, strict_value.host_number_type }, { strict_value.host_number_type }),
	["-"] = exprs.host_applicative(function(a, b)
		return a - b
	end, { strict_value.host_number_type, strict_value.host_number_type }, { strict_value.host_number_type }),
	["*"] = exprs.host_applicative(function(a, b)
		return a * b
	end, { strict_value.host_number_type, strict_value.host_number_type }, { strict_value.host_number_type }),
	["/"] = exprs.host_applicative(function(a, b)
		return a / b
	end, { strict_value.host_number_type, strict_value.host_number_type }, { strict_value.host_number_type }),
	["%"] = exprs.host_applicative(function(a, b)
		return a % b
	end, { strict_value.host_number_type, strict_value.host_number_type }, { strict_value.host_number_type }),
	neg = exprs.host_applicative(function(a)
		return -a
	end, { strict_value.host_number_type }, { strict_value.host_number_type }),

	--["<"] = evaluator.host_applicative(function(args)
	--  return { variant = (args[1] < args[2]) and 1 or 0, arg = types.unit_val }
	--end, types.tuple {types.number, types.number}, types.cotuple({types.unit, types.unit})),
	--["=="] = evaluator.host_applicative(function(args)
	--  return { variant = (args[1] == args[2]) and 1 or 0, arg = types.unit_val }
	--end, types.tuple {types.number, types.number}, types.cotuple({types.unit, types.unit})),

	--["do"] = evaluator.host_operative(do_block),
	let = exprs.host_operative(let_impl, "let_impl"),
	mk = exprs.host_operative(mk_impl, "mk_impl"),
	switch = exprs.host_operative(switch_impl, "switch_impl"),
	enum = exprs.host_operative(enum_impl, "enum_impl"),
	["debug-trace"] = exprs.host_operative(debug_trace_impl, "debug_trace_impl"),
	["dump-context"] = exprs.host_operative(dump_context_impl, "dump_context_impl"),
	--record = exprs.host_operative(record_build, "record_build"),
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
	--["into-operative"] = exprs.host_operative(into_operative_impl, "into_operative_impl"),
	-- ["hackhack-host-term-of-inner"] = terms.inferrable_term.typed(
	-- 	host_term_of_inner_type,
	-- 	usage_array(),
	-- 	typed.literal(strict_value.host_value(host_term_of_inner))
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

local function traverse(desc, len, elems)
	len = len or 0
	elems = elems or {}
	local constructor, arg = desc:unwrap_enum_value()
	if constructor == terms.DescCons.empty then
		return len, elems
	elseif constructor == terms.DescCons.cons then
		local elements = arg:unwrap_tuple_value()
		local next_desc = elements[1]
		len = len + 1
		elems[len] = elements[2]
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
	local names = debug_array()
	for _, name in head_names:ipairs() do
		names:append(name)
	end
	names:append(var_debug("#_", U.anchor_here()))
	for _, name in tail_names:ipairs() do
		names:append(name)
	end
	-- convert to just tuple of tail
	local tail_args = typed_array()
	for i = 1, tail_n do
		-- 1 for closure argument (passed to tuple_elim)
		-- head_n for head
		tail_args:append(typed.bound_variable(1 + head_n + i, names[1 + head_n + i]))
	end
	local body = typed.tuple_elim(
		names:map(name_array, function(n)
			return n.name
		end),
		names,
		typed.bound_variable(1, var_debug("", U.anchor_here())),
		head_n + tail_n,
		typed.application(typed.literal(elem), typed.tuple_cons(tail_args))
	)
	local elem_wrap = terms.flex_value.closure(
		"#tuple-desc-concat",
		body,
		terms.flex_runtime_context(),
		var_debug("#tuple-desc-concat", U.anchor_here())
	)
	return terms.cons(desc, elem_wrap)
end

local function tuple_desc_concat(head, tail)
	local head_n, head_elems = traverse(head)
	local tail_n, tail_elems = traverse(tail)
	local head_last = head_elems[1]
	local _, head_code, _, _ = head_last:unwrap_closure()
	local head_names
	if head_code:is_tuple_elim() then
		_, head_names, _, _, _ = head_code:unwrap_tuple_elim()
	else
		head_names = debug_array()
		for i = 1, head_n do
			head_names[i] = var_debug("head_unk_" .. tostring(i), U.anchor_here())
		end
	end
	local desc = head
	for i = tail_n, 1, -1 do
		local tail_n_now = tail_n - i
		local elem = tail_elems[i]
		local _, tail_code, _, _ = elem:unwrap_closure()
		local tail_names
		if tail_code:is_tuple_elim() then
			_, tail_names, _, _, _ = tail_code:unwrap_tuple_elim()
		else
			tail_names = debug_array()
			for i = 1, tail_n do
				tail_names[i] = var_debug("tail_unk_" .. tostring(i), U.anchor_here())
			end
		end
		desc = tuple_desc_elem(desc, elem, head_n, head_names, tail_n_now, tail_names)
	end
	return desc
end

local host_if = (function()
	local debug_arg = terms.var_debug("#host-if-param", U.anchor_here())
	local debug_subject = terms.var_debug("#host-if-subject", U.anchor_here())
	local debug_consequent = terms.var_debug("#host-if-consequent", U.anchor_here())
	local debug_alternate = terms.var_debug("#host-if-alternate", U.anchor_here())
	local debug_elements = debug_array(debug_subject, debug_consequent, debug_alternate)
	return terms.flex_value.closure(
		"#host-if-param",
		typed.tuple_elim(
			debug_elements:map(name_array, function(n)
				return n.name
			end),
			debug_elements,
			typed.bound_variable(1, debug_arg),
			3,
			typed.host_if(
				typed.bound_variable(2, debug_subject),
				typed.bound_variable(3, debug_consequent),
				typed.bound_variable(4, debug_alternate)
			)
		),
		terms.flex_runtime_context(),
		debug_arg
	)
end)()

local function convert_desc(desc)
	local constructor, arg = desc:unwrap_enum_value()
	if constructor == terms.DescCons.empty then
		return desc
	elseif constructor == terms.DescCons.cons then
		local elements = arg:unwrap_tuple_value()
		local next_desc, type_fun = elements[1], elements[2]
		local convert_next = convert_desc(next_desc)
		local convert_type = terms.flex_value.variance_type(
			evaluator.apply_value(
				type_fun,
				terms.flex_value.stuck(terms.stuck_value.free(terms.free.unique {})),
				terms.typechecking_context()
			)
		)
		local convert_type_fun = terms.flex_value.closure(
			"#tuple-prefix",
			terms.typed_term.literal(convert_type),
			terms.flex_runtime_context(),
			var_debug("#tuple-prefix", U.anchor_here())
		)
		evaluator.verify_placeholder_lite(convert_type_fun, terms.typechecking_context())
		return terms.flex_value.enum_value(
			terms.DescCons.cons,
			terms.flex_value.tuple_value(flex_value_array(convert_next, convert_type_fun))
		)
	else
		error "unknown tuple desc constructor"
	end
end

local function convert_sig(sig)
	local param_type, _, _, _ = sig:unwrap_pi()
	local param_desc = param_type:unwrap_tuple_type()
	return terms.flex_value.tuple_type(convert_desc(param_desc))
end

local function desc_length(desc, len)
	len = len or 0
	local constructor, arg = desc:unwrap_enum_value()
	if constructor == terms.DescCons.empty then
		return len
	elseif constructor == terms.DescCons.cons then
		local elements = arg:unwrap_tuple_value()
		local next_desc = elements[1]
		return desc_length(next_desc, len + 1)
	else
		error("unknown tuple desc constructor")
	end
end
local function new_host_type_family(unique_id, sig, variance)
	local param_type, _, _, _ = sig:unwrap_pi()
	local param_desc = param_type:unwrap_tuple_type()
	local nparams = desc_length(param_desc)

	local variance_elems = variance:unwrap_tuple_value()
	local variances = {}
	for i, v in variance_elems:ipairs() do
		variances[i] = v:unwrap_host_value()
	end

	local srel = evaluator.IndepTupleRelation(table.unpack(variances))
	evaluator.register_host_srel(unique_id, srel)

	local params = typed_array()
	local param_names = debug_array()
	for i = 1, nparams do
		local info = var_debug("#type-family-A-" .. tostring(i), U.anchor_here())
		params:append(terms.typed_term.bound_variable(i + 1, info))
		param_names:append(info)
	end
	local info = var_debug("body", U.anchor_here())
	local body = terms.typed_term.tuple_elim(
		param_names:map(name_array, function(n)
			return n.name
		end),
		param_names,
		terms.typed_term.bound_variable(1, info),
		nparams,
		terms.typed_term.host_user_defined_type_cons(unique_id, params)
	)
	return terms.flex_value.closure("#type-family-B", body, terms.flex_runtime_context(), info)
end

---@param subject flex_value
local function get_host_func_res(subject, valid)
	local param_type, result_type, result_info = subject:unwrap_host_function_type()
	local typed_array = terms_gen.declare_array(terms.typed_term)

	local result_dbg = var_debug("#result_type", U.anchor_here())
	local arg_dbg = var_debug("#res_arg", U.anchor_here())
	local tuple_build = terms.typed_term.tuple_cons(
		typed_array(
			terms.typed_term.host_wrap(
				terms.typed_term.application(
					terms.typed_term.bound_variable(1, result_dbg),
					terms.typed_term.bound_variable(2, arg_dbg)
				)
			),
			terms.typed_term.literal(terms.strict_value.host_value(nil))
		)
	)
	local ctx = terms.flex_runtime_context():append(result_type, "#res_arg", result_dbg)
	return terms.flex_value.closure("#TEST-1", tuple_build, ctx, arg_dbg)
end

local function tuple_to_host_tuple_inner(_type, _valid, val)
	local elems = val:unwrap_tuple_value()
	local leading = terms_gen.declare_array(terms_gen.any_lua_type)()
	local stuck = false
	local stuck_elem = nil
	local trailing = terms_gen.declare_array(terms.flex_value)()
	for _, v in ipairs(elems) do
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
		return terms.flex_value.host_tuple_value(leading)
	else
		return terms.flex_value.stuck(terms.stuck_value.host_tuple(leading, stuck_elem, trailing))
	end
end

local core_operative_type = (function()
	local debug_arg = terms.var_debug("#args", U.anchor_here())
	local debug_userdata = terms.var_debug("userdata", U.anchor_here())
	local debug_handler = terms.var_debug("handler", U.anchor_here())
	local debug_elements = debug_array(debug_userdata, debug_handler)
	return terms.flex_value.closure(
		debug_arg.name,
		terms.typed_term.tuple_elim(
			debug_elements:map(name_array, function(n)
				return n.name
			end),
			debug_elements,
			terms.typed_term.bound_variable(1, debug_arg),
			2,
			terms.typed_term.operative_type_cons(
				terms.typed_term.bound_variable(3, debug_handler),
				terms.typed_term.bound_variable(2, debug_userdata) --TODO: fix the order on this
			)
		),
		terms.flex_runtime_context(),
		debug_arg
	)
end)()

local core_operative = (function()
	local debug_arg = terms.var_debug("#args", U.anchor_here())
	local debug_ud = terms.var_debug("ud", U.anchor_here())
	local debug_handler = terms.var_debug("handler", U.anchor_here())
	local debug_elements = debug_array(debug_ud, debug_handler)
	return terms.flex_value.closure(
		debug_arg.name,
		terms.typed_term.tuple_elim(
			debug_elements:map(name_array, function(n)
				return n.name
			end),
			debug_elements,
			terms.typed_term.bound_variable(1, debug_arg),
			2,
			terms.typed_term.operative_cons(terms.typed_term.bound_variable(2, debug_ud))
		),
		terms.flex_runtime_context(),
		debug_arg
	)
end)()

local string_array = gen.declare_array(gen.builtin_string)
local debug_array = gen.declare_array(terms.var_debug)

---@param fn_op fun(bound_variables: typed[]) : integer, typed
---@param name string
---@param ... string
---@return strict_value
local function gen_base_operator(fn_op, name, ...)
	local argname = name .. "-arg"
	local debug_arg = terms.var_debug(argname, U.anchor_here())
	local names = string_array(...)
	local debug_names = names:map(debug_array, function(n)
		return terms.var_debug(n, U.anchor_here())
	end)
	local bound_vars = {}
	for i, v in ipairs(debug_names) do
		table.insert(bound_vars, terms.typed_term.bound_variable(1 + i, v))
	end

	local count, res = fn_op(bound_vars)
	return terms.strict_value.closure(
		argname,
		terms.typed_term.tuple_elim(names, debug_names, terms.typed_term.bound_variable(1, debug_arg), count, res),
		terms.strict_runtime_context(),
		debug_arg
	)
end

---@return strict_value
local function contravariant()
	return gen_base_operator(function(vars)
		return 1, terms.typed_term.variance_cons(terms.typed_term.literal(terms.strict_value.host_value(true)), vars[1])
	end, "#contravariant", "base")
end

local base_env = {
	ascribed_segment_tuple_desc = ascribed_segment_tuple_desc,
	create = create,
	host_if = host_if,
	tuple_desc_concat = tuple_desc_concat,
	convert_sig = convert_sig,
	new_host_type_family = new_host_type_family,
	tuple_to_host_tuple_inner = tuple_to_host_tuple_inner,
	get_host_func_res = get_host_func_res,
	gen_base_operator = gen_base_operator,
	core_operative_type = core_operative_type,
	core_operative = core_operative,
}
local internals_interface = require "internals-interface"
internals_interface.base_env = base_env
return base_env
