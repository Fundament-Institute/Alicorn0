local environment = require "./environment"
local treemap = require "./lazy-prefix-tree"
local types = require "./typesystem"
local metalang = require "./metalanguage"
local utils = require "./reducer-utils"
local exprs = require "./alicorn-expressions"
local terms = require "./terms"
local gen = require "./terms-generators"
local evaluator = require "./evaluator"

local p = require "pretty-print".prettyPrint

local function do_block_pair_handler(env, a, b)
	local ok, val, newenv = a:match({
		evaluator.evaluates(metalang.accept_handler, env),
	}, metalang.failure_handler, nil)
	if not ok then
		return false, val
	end
	--print("do block pair handler", ok, val, newenv, b)
	return true, true, val, newenv, b
end

local function do_block_nil_handler(env)
	return true, false, nil, env
end

local function do_block(syntax, env)
	local newenv = env:child_scope()
	local ok, val, newenv = syntax:match({
		evaluator.block(metalang.accept_handler, newenv),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, val
	end
	return ok, val, env:exit_child_scope(newenv)
end

local function let_bind(syntax, env)
	local ok, name, tail = syntax:match({
		metalang.listtail(
			metalang.accept_handler,
			metalang.oneof(
				metalang.accept_handler,
				metalang.issymbol(metalang.accept_handler),
				metalang.list_many(metalang.accept_handler, metalang.issymbol(metalang.accept_handler))
			),
			metalang.symbol_exact(metalang.accept_handler, "=")
		),
	}, metalang.failure_handler, nil)

	if not ok then
		return false, name
	end

	local bind
	ok, bind = tail:match({
		metalang.listmatch(metalang.accept_handler, exprs.inferred_expression(utils.accept_with_env, env)),
		exprs.inferred_expression(utils.accept_with_env, env),
	}, metalang.failure_handler, nil)

	if not ok then
		return false, bind
	end

	env = bind.env
	if not env or not env.get then
		p(env)
		error("env in let_bind isn't an env")
	end

	if type(name) == "table" then
		print("binding destructuring with let")
		p(name)
		local tupletype = gen.declare_array(gen.builtin_string)
		env = env:bind_local(terms.binding.tuple_elim(tupletype(unpack(name)), bind.val))
	else
		env = env:bind_local(terms.binding.let(name, bind.val))
	end

	return true,
		terms.inferrable_term.typed(
			terms.unit_type,
			gen.declare_array(gen.builtin_number)(),
			terms.typed_term.literal(terms.unit_val)
		),
		env
end

local function record_threaded_element_acceptor(_, name, exprenv)
	return true, { name = name, expr = exprenv.val }, exprenv.env
end

local function record_threaded_element(env)
	return metalang.listmatch(
		record_threaded_element_acceptor,
		metalang.issymbol(metalang.accept_handler),
		metalang.symbol_exact(metalang.accept_handler, "="),
		exprs.inferred_expression(utils.accept_with_env, env)
	)
end

local function record_build(syntax, env)
	local ok, defs, env = syntax:match({
		metalang.list_many_threaded(metalang.accept_handler, record_threaded_element, env),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, defs
	end
	local map = gen.declare_map(gen.builtin_string, terms.inferrable_term)()
	for i, v in ipairs(defs) do
		map[v.name] = v.expr
	end
	return true, terms.inferrable_term.record_cons(map), env
end

---@param syntax any
---@param env Environment
---@return boolean
---@return any
---@return Environment
local function intrinsic(syntax, env)
	local ok, str_env, syntax = syntax:match({
		metalang.listtail(
			metalang.accept_handler,
			exprs.inferred_expression(utils.accept_with_env, env),
			metalang.symbol_exact(metalang.accept_handler, ":")
		),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, str_env
	end
	env = str_env.env
	if not env then
		error "env nil in base-env.intrinsic"
	end
	local str = terms.checkable_term.inferrable(str_env.val) -- workaround for not having exprs.checked_expression yet
	local ok, type_env = syntax:match({
		metalang.listmatch(metalang.accept_handler, exprs.inferred_expression(utils.accept_with_env, env)),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, type_env
	end
	local type, env = type_env.val, type_env.env
	if not env then
		error "env nil in base-env.intrinsic"
	end
	return true,
		terms.inferrable_term.prim_intrinsic(str, type--[[terms.checkable_term.inferrable(type)]], syntax.anchor),
		env
end

--evaluator.define_operate(
--  basic_fn_kind,
--  function(self, operands, env)
--    local ok, args, env = operands:match(
--      {
--        evaluator.collect_tuple(metalang.accept_handler, env)
--      },
--      metalang.failure_handler,
--      nil
--    )
--    if not ok then return ok, args end
--    if #args.type.params ~= #self.val.argnames then return false, "argument count mismatch" end
--    local bindings = {}
--    for i = 1, #args.type.params do
--      bindings[self.val.argnames[i]] = environment.new_store{type = args.type.params[i], val = args.val[i]}
--    end
--    local callenv = environment.new_env {
--      locals = treemap.build(bindings),
--      nonlocals = self.val.enclosing_bindings,
--      carrier = env.carrier,
--      perms = self.val.enclosing_perms
--    }
--    local ok, res, resenv = self.val.body:match(
--      {
--        evaluator.block(metalang.accept_handler, callenv)
--      },
--      metalang.failure_handler,
--      nil
--    )
--    if not ok then return ok, res end
--    return ok, res, environment.new_env {locals = env.locals, nonlocals = env.nonlocals, carrier = resenv.carrier, perms = env.perms}
--
--end)

local function basic_fn(syntax, env)
	local ok, args, body = syntax:match({
		metalang.ispair(metalang.accept_handler),
	}, metalang.failure_handler, nil)
	if not ok then
		return false, args
	end
	-- print "defining function"
	-- p(args)
	-- p(body)
	local ok, names = args:match({
		metalang.list_many(metalang.accept_handler, metalang.issymbol(metalang.accept_handler)),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, names
	end
	local defn = {
		enclosing_bindings = env.bindings,
		enclosing_perms = env.perms,
		body = body,
		argnames = names,
	}
	return true, { type = basic_fn_type, val = defn }, env
end

local function tuple_type_impl(syntax, env)
	local ok, typeargs, env = syntax:match({
		evaluator.collect_tuple(metalang.accept_handler, env),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, typeargs
	end
	for i, t in ipairs(typeargs.type.params) do
		if t ~= types.type then
			return false, "tuple-type was provided something that wasn't a type"
		end
	end
	return true, { type = types.type, val = types.tuple(typeargs.val) }, env
end
local function tuple_of_impl(syntax, env)
	local ok, components, env = syntax:match({
		evaluator.collect_tuple(metalang.accept_handler, env),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, components
	end
	return true, components, env
end

local pure_ascribed_name_with_tail = metalang.reducer(function(syntax, env)
	local ok, name, type_env, tail = syntax:match({
		metalang.listtail(
			metalang.accept_handler,
			metalang.issymbol(metalang.accept_handler),
			metalang.symbol_exact(metalang.accept_handler, ":"),
			exprs.inferred_expression(utils.accept_with_env, env)
		),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, name
	end
	return true, name, type_env.val, type_env.env, tail
end, "pure_ascribed_name_with_tail")

local ascribed_name_with_tail = metalang.reducer(function(syntax, env, prev, names)
	-- print("ascribed_name trying")
	-- p(syntax)
	-- print(prev:pretty_print())
	-- print("is env an environment? (start of ascribed name)")
	-- print(env.get)
	-- print(env.enter_block)
	---@cast env Environment
	local shadowed, env = env:enter_block()
	env = env:bind_local(terms.binding.annotated_lambda("#prev", prev, syntax.anchor, terms.visibility.explicit))
	local ok, prev_binding = env:get("#prev")
	if not ok then
		error "#prev should always be bound, was just added"
	end
	env = env:bind_local(terms.binding.tuple_elim(names, prev_binding))
	local ok, name, val, env, tail =
		syntax:match({ pure_ascribed_name_with_tail(metalang.accept_handler, env) }, metalang.failure_handler, nil)
	if not ok then
		return ok, name
	end
	---@type Environment
	local env, val = env:exit_block(val, shadowed)
	-- print("is env an environment? (end of ascribed name)")
	-- print(env.get)
	-- print(env.enter_block)
	return true, name, val, env, tail
end, "ascribed_name_with_tail")

local ascribed_name = metalang.reducer(function(syntax, env, prev, names)
	local ok, name, val, env = syntax:match({
		metalang.list_tail_ends(
			metalang.accept_handler,
			ascribed_name_with_tail(metalang.accept_handler, env, prev, names)
		),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, name
	end
	return true, name, val, env
end, "ascribed_name")

local tupleof_ascribed_names_inner = metalang.reducer(function(syntax, env, termination, build_type_term)
	local inf_array = gen.declare_array(terms.inferrable_term)
	local function tup_cons(...)
		return terms.inferrable_term.tuple_cons(inf_array(...))
	end
	local function cons(...)
		return terms.inferrable_term.enum_cons(terms.value.tuple_defn_type(terms.value.star(0)), "cons", tup_cons(...))
	end
	local empty = terms.inferrable_term.enum_cons(terms.value.tuple_defn_type(terms.value.star(0)), "empty", tup_cons())
	local args = empty

	local names = gen.declare_array(gen.builtin_string)()

	local ok = true

	ok, names, args, env, tail = syntax:match({
		metalang.list_many_threaded_until(function(_, vals, thread, tail)
			return true, thread.names, build_type_term(thread.args), thread.env, tail
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
		}, termination),
	}, metalang.failure_handler, nil)

	if not ok then
		return ok, names
	end

	return true, { names = names, args = args, env = env }, tail
end, "tupleof_ascribed_names_inner")

local tupleof_ascribed_names = metalang.reducer(function(syntax, env, termination)
	local function build_type_term(args)
		return terms.inferrable_term.tuple_type(args)
	end
	return syntax:match({
		tupleof_ascribed_names_inner(metalang.accept_handler, env, termination, build_type_term),
	}, metalang.failure_handler, nil)
end, "tupleof_ascribed_names")

local prim_tupleof_ascribed_names = metalang.reducer(function(syntax, env, termination)
	local function build_type_term(args)
		return terms.inferrable_term.prim_tuple_type(args)
	end
	return syntax:match({
		tupleof_ascribed_names_inner(metalang.accept_handler, env, termination, build_type_term),
	}, metalang.failure_handler, nil)
end, "prim_tupleof_ascribed_names")

local ascribed_segment = metalang.reducer(function(syntax, env, termination)
	local single, tail, name, type_val, type_env

	local ok = true

	single, name, type_val, type_env, tail = syntax:match({
		pure_ascribed_name_with_tail(metalang.accept_handler, env),
	}, metalang.failure_handler, nil)

	local names, args

	if single then
		ok, tail = tail:match({
			metalang.listtail(metalang.accept_handler, termination),
			-- if termination is nil listtail will fail to match. so this is redundant and SHOULDN'T activate
			-- but I don't know how to make it not necessary
			termination,
		}, metalang.failure_handler, env)

		if not ok then
			return false, "only one bare ascribed name permitted"
		end

		env = type_env
		args = type_val
		names = name
	elseif not single then
		local thread
		ok, thread, tail = syntax:match({
			tupleof_ascribed_names(metalang.accept_handler, env, termination),
		}, metalang.failure_handler, nil)

		if not ok then
			return ok, thread
		end

		env = thread.env
		args = thread.args
		names = thread.names
	end

	return true, { single = single, names = names, args = args, env = env }, tail
end, "ascribed_segment")

local function prim_func_type_pair_handler(env, a, b)
	local ok, val, env =
		a:match({ exprs.inferred_expression(metalang.accept_handler, env) }, metalang.failure_handler, nil)
	if not ok then
		return false, val
	end
	return true, true, val, b, env
end

local function prim_func_type_empty_handler(env)
	return true, false, nil, nil, env
end

local prim_func_type_impl_reducer = metalang.reducer(function(syntax, env)
	local pft_anchor = syntax.anchor

	if not env or not env.enter_block then
		error "env isn't an environment in prim_func_type_impl_reducer"
	end

	local ok, thread, syntax = syntax:match({
		prim_tupleof_ascribed_names(metalang.accept_handler, env, metalang.symbol_exact(metalang.accept_handler, "->")),
	}, metalang.failure_handler, nil)

	if not ok then
		return ok, thread
	end

	env = thread.env
	local args = thread.args
	local names = thread.names

	print("moving on to return type")
	local shadowed, env = env:enter_block()

	-- syntax.anchor can be nil so we fall back to the anchor for the start of this prim func type if needed
	env = env:bind_local(terms.binding.annotated_lambda("#prim-func-arguments", args, syntax.anchor or pft_anchor, terms.visibility.explicit))
	local ok, arg = env:get("#prim-func-arguments")
	env = env:bind_local(terms.binding.tuple_elim(names, arg))

	ok, thread, tail = syntax:match({
		prim_tupleof_ascribed_names(metalang.accept_handler, env, metalang.isnil(metalang.accept_handler)),
	}, metalang.failure_handler, nil)

	if not ok then
		return ok, thread
	end

	env = thread.env
	local results = thread.args
	local names = thread.names

	local env, fn_res_term = env:exit_block(results, shadowed)
	local fn_type_term = terms.inferrable_term.prim_function_type(args, fn_res_term)
	print("reached end of function type construction")
	if not env.enter_block then
		error "env isn't an environment at end in prim_func_type_impl_reducer"
	end
	return true, fn_type_term, env
end, "prim_func_type_impl")

-- TODO: abstract so can reuse for func type and prim func type
---@param syntax any
---@param env Environment
---@return boolean
---@return unknown
---@return unknown|nil
local function prim_func_type_impl(syntax, env)
	print("in prim_func_type_impl")
	local ok, fn_type_term, env =
		syntax:match({ prim_func_type_impl_reducer(metalang.accept_handler, env) }, metalang.failure_handler, env)
	if not ok then
		return ok, fn_type_term
	end
	print("finished matching prim_func_type_impl and got:")
	print("ok:", ok)
	print("fn_type_term: (inferrable term follows)")
	print(fn_type_term:pretty_print(env.typechecking_context))
	if not env or not env.enter_block then
		error "env isn't an environment at end in prim_func_type_impl"
	end
	return ok, fn_type_term, env
end

local forall_type_impl_reducer = metalang.reducer(function(syntax, env)
	local usage_array = gen.declare_array(gen.builtin_number)

	if not env.enter_block then
		error "env isn't an environment in forall_type_impl_reducer"
	end

	local single, args, names, thread
	local ok = true

	ok, thread, syntax = syntax:match(
		{ ascribed_segment(metalang.accept_handler, env, metalang.symbol_exact(metalang.accept_handler, "->")) },
		metalang.failure_handler,
		nil
	)

	if not ok then
		return false, thread
	end
	single, args, names, env = thread.single, thread.args, thread.names, thread.env

	print("moving on to return type")

	local shadowed, env = env:enter_block()

	-- TODO: use correct name in lambda parameter instead of adding an extra let
	env = env:bind_local(terms.binding.annotated_lambda("#forall-arguments", args, syntax.anchor, terms.visibility.explicit))
	local ok, arg = env:get("#forall-arguments")
	if single then
		env = env:bind_local(terms.binding.let(names, arg))
	else
		env = env:bind_local(terms.binding.tuple_elim(names, arg))
	end

	local results

	ok, thread, syntax = syntax:match(
		{ ascribed_segment(metalang.accept_handler, env, metalang.isnil(metalang.accept_handler)) },
		metalang.failure_handler,
		nil
	)

	if not ok then
		return false, thread
	end
	single, results, names, env = thread.single, thread.args, thread.names, thread.env

	local env, fn_res_term = env:exit_block(results, shadowed)
	local fn_type_term = terms.inferrable_term.pi(
		args,
		terms.checkable_term.inferrable(
			terms.inferrable_term.typed(
				terms.value.param_info_type,
				usage_array(),
				terms.typed_term.literal(terms.value.param_info(terms.value.visibility(terms.visibility.explicit)))
			)
		),
		fn_res_term,
		terms.checkable_term.inferrable(
			terms.inferrable_term.typed(
				terms.value.result_info_type,
				usage_array(),
				terms.typed_term.literal(terms.value.result_info(terms.result_info(terms.purity.pure)))
			)
		)
	)

	print("reached end of function type construction")
	if not env.enter_block then
		error "env isn't an environment at end in prim_func_type_impl_reducer"
	end
	return true, fn_type_term, env
end, "forall_type_impl")

-- TODO: abstract so can reuse for func type and prim func type
---@param syntax any
---@param env Environment
---@return boolean
---@return unknown
---@return unknown|nil
local function forall_type_impl(syntax, env)
	print("in forall_type_impl")
	local ok, fn_type_term, env =
		syntax:match({ forall_type_impl_reducer(metalang.accept_handler, env) }, metalang.failure_handler, env)
	if not ok then
		return ok, fn_type_term
	end
	print("finished matching prim_func_type_impl and got")
	print(fn_type_term:pretty_print(env.typechecking_context))
	if not env.enter_block then
		error "env isn't an environment at end in prim_func_type_impl"
	end
	return ok, fn_type_term, env
	-- parse sequence of ascribed names, arrow, then sequence of ascribed names
	-- for each ascribed name:
	-- enter a block, perform lambda binding, perform tuple destrucutring binding, parse out the type of the ascription

	--local ok,
end

---Constrains a type by using a checked expression goal and producing an annotated inferrable term
---(the prim-number 5) -> produces inferrable_term.annotated(lit(5), lit(prim-number))
---@param syntax any
---@param env Environment
---@return boolean
---@return unknown
---@return unknown|nil
local function the_operative_impl(syntax, env)
	local ok, type_inferrable_term, tail = syntax:match({
		metalang.listtail(metalang.accept_handler, exprs.inferred_expression(metalang.accept_handler, env)),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, type, tail
	end

	local type_of_typed_term, usages, type_typed_term = evaluator.infer(type_inferrable_term, env.typechecking_context)
	local evaled_type = evaluator.evaluate(type_typed_term, env.typechecking_context.runtime_context)

	print("type_inferrable_term: (inferrable term follows)")
	print(type_inferrable_term:pretty_print(env.typechecking_context))
	print("evaled_type: (value term follows)")
	print(evaled_type)
	print("tail", tail)
	local ok, val, tail = tail:match({
		metalang.ispair(metalang.accept_handler),
	}, metalang.failure_handler, nil)
	if not ok then
		return false, val
	end
	local ok, val, env = val:match({
		exprs.expression(
			metalang.accept_handler,
			-- FIXME: do we infer here if evaled_type is stuck / a placeholder?
			exprs.ExpressionArgs.new(terms.expression_goal.check(evaled_type), env)
		),
	}, metalang.failure_handler, nil)
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
---@param syntax any
---@param env Environment
---@return boolean
---@return unknown
---@return unknown|nil
local function apply_operative_impl(syntax, env)
	local ok, fn, tail = syntax:match({ metalang.ispair(metalang.accept_handler) }, metalang.failure_handler, nil)
	if not ok then
		return ok, fn
	end

	local ok, fn_inferrable_term, env =
		fn:match({ exprs.inferred_expression(metalang.accept_handler, env) }, metalang.failure_handler, nil)
	if not ok then
		return ok, fn_inferrable_term
	end

	local type_of_fn, usages, fn_typed_term = evaluator.infer(fn_inferrable_term, env.typechecking_context)

	local param_type, _
	if type_of_fn:is_pi() then
		param_type, _, _, _ = type_of_fn:unwrap_pi()
	elseif type_of_fn:is_prim_function_type() then
		local param_type, _ = type_of_fn:unwrap_prim_function_type()
	else
		error "unknown fn type for apply operative"
	end

	local ok, args_inferrable_term = tail:match({
		metalang.listmatch(
			metalang.accept_handler,
			exprs.expression(
				utils.accept_with_env,
				-- FIXME: do we infer here if evaled_type is stuck / a placeholder?
				exprs.ExpressionArgs.new(terms.expression_goal.check(param_type), env)
			)
		),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, fn_inferrable_term
	end

	local inf_term = args_inferrable_term.val
	if terms.inferrable_term.value_check(inf_term) == true then
		inf_term = terms.checkable_term.inferrable(inf_term)
	end
	return true,
		terms.inferrable_term.application(terms.inferrable_term.typed(type_of_fn, usages, fn_typed_term), inf_term),
		args_inferrable_term.env
end

---@param syntax any
---@param env Environment
---@return boolean
---@return unknown
---@return unknown|nil
local function lambda_impl(syntax, env)
	local ok, thread, tail = syntax:match({
		metalang.listtail(
			metalang.accept_handler,
			ascribed_segment(metalang.accept_handler, env, metalang.isnil(metalang.accept_handler))
		),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, thread
	end

	local single, args, names, env = thread.single, thread.args, thread.names, thread.env

	local shadow, inner_env = env:enter_block()
	-- TODO: use correct name in lambda parameter instead of adding an extra let
	inner_env = inner_env:bind_local(terms.binding.annotated_lambda("#lambda-arguments", thread.args, syntax.anchor, terms.visibility.explicit))
	local _, arg = inner_env:get("#lambda-arguments")
	if single then
		inner_env = inner_env:bind_local(terms.binding.let(names, arg))
	else
		inner_env = inner_env:bind_local(terms.binding.tuple_elim(names, arg))
	end
	local ok, expr, env = tail:match(
		{ exprs.block(metalang.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, inner_env)) },
		metalang.failure_handler,
		nil
	)
	if not ok then
		return ok, expr
	end
	local resenv, term = env:exit_block(expr, shadow)
	return true, term, resenv
end


---@param syntax any
---@param env Environment
---@return boolean
---@return unknown
---@return unknown|nil
local function lambda_impl_implicit(syntax, env)
	local ok, thread, tail = syntax:match({
		metalang.listtail(
			metalang.accept_handler,
			ascribed_segment(metalang.accept_handler, env, metalang.isnil(metalang.accept_handler))
		),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, thread
	end

	local single, args, names, env = thread.single, thread.args, thread.names, thread.env

	local shadow, inner_env = env:enter_block()
	-- TODO: use correct name in lambda parameter instead of adding an extra let
	inner_env = inner_env:bind_local(terms.binding.annotated_lambda("#lambda-arguments", thread.args, syntax.anchor, terms.visibility.implicit))
	local _, arg = inner_env:get("#lambda-arguments")
	if single then
		inner_env = inner_env:bind_local(terms.binding.let(names, arg))
	else
		inner_env = inner_env:bind_local(terms.binding.tuple_elim(names, arg))
	end
	local ok, expr, env = tail:match(
		{ exprs.block(metalang.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, inner_env)) },
		metalang.failure_handler,
		nil
	)
	if not ok then
		return ok, expr
	end
	local resenv, term = env:exit_block(expr, shadow)
	return true, term, resenv
end

local value = terms.value
local typed = terms.typed_term

local usage_array = gen.declare_array(gen.builtin_number)
local val_array = gen.declare_array(value)

local function lit_term(val, typ)
	return terms.inferrable_term.typed(typ, usage_array(), terms.typed_term.literal(val))
end

local function startype_impl(syntax, env)
	local ok, level_val = syntax:match({
		metalang.listmatch(metalang.accept_handler, metalang.isvalue(metalang.accept_handler)),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, level_val
	end
	if level_val.type ~= "f64" then
		return false, "literal must be a number for type levels"
	end
	if level_val.val % 1 ~= 0 then
		return false, "literal must be an integer for type levels"
	end
	local term =
		terms.inferrable_term.typed(value.star(level_val.val + 1), usage_array(), terms.typed_term.star(level_val.val))

	return true, term, env
end

local function val_tup_cons(...)
	return value.tuple_value(val_array(...))
end
local function val_desc_elem(x)
	return value.enum_value("cons", x)
end
local val_desc_empty = value.enum_value("empty", val_tup_cons())

-- eg typed.prim_wrap, typed.prim_wrapped_type
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
				val_desc_elem(
					val_tup_cons(
						val_desc_elem(
							val_tup_cons(
								val_desc_empty,
								value.closure(
									pname_type,
									typed.tuple_elim(names0, typed.bound_variable(1), 0, typed.star(10)),
									terms.runtime_context()
								)
							)
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
				)
			),
			value.param_info(value.visibility(terms.visibility.explicit)),
			value.closure(
				pname_type,
				typed.tuple_elim(names2, typed.bound_variable(1), 2, type_fn(typed.bound_variable(2))),
				terms.runtime_context()
			),
			value.result_info(terms.result_info(terms.purity.pure))
		)
	)
end

-- eg typed.prim_unwrap, typed.prim_wrapped_type
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
				val_desc_elem(
					val_tup_cons(
						val_desc_elem(
							val_tup_cons(
								val_desc_empty,
								value.closure(
									pname_type,
									typed.tuple_elim(names0, typed.bound_variable(1), 0, typed.star(10)),
									terms.runtime_context()
								)
							)
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
				)
			),
			value.param_info(value.visibility(terms.visibility.explicit)),
			value.closure(
				pname_type,
				typed.tuple_elim(names2, typed.bound_variable(1), 2, typed.bound_variable(2)),
				terms.runtime_context()
			),
			value.result_info(terms.result_info(terms.purity.pure))
		)
	)
end

-- eg typed.prim_wrapped_type,
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
				val_desc_elem(
					val_tup_cons(
						val_desc_empty,
						value.closure(
							pname_type,
							typed.tuple_elim(names0, typed.bound_variable(1), 0, typed.star(10)),
							terms.runtime_context()
						)
					)
				)
			),
			value.param_info(value.visibility(terms.visibility.explicit)),
			value.closure(
				pname_type,
				typed.tuple_elim(names1, typed.bound_variable(1), 1, typed.literal(value.prim_type_type)),
				terms.runtime_context()
			),
			value.result_info(terms.result_info(terms.purity.pure))
		)
	)
end

local core_operations = {
	["+"] = exprs.primitive_applicative(function(a, b)
		return a + b
	end, { value.prim_number_type, value.prim_number_type }, { value.prim_number_type }),
	["-"] = exprs.primitive_applicative(function(a, b)
		return a - b
	end, { value.prim_number_type, value.prim_number_type }, { value.prim_number_type }),
	["*"] = exprs.primitive_applicative(function(a, b)
		return a * b
	end, { value.prim_number_type, value.prim_number_type }, { value.prim_number_type }),
	["/"] = exprs.primitive_applicative(function(a, b)
		return a / b
	end, { value.prim_number_type, value.prim_number_type }, { value.prim_number_type }),
	["%"] = exprs.primitive_applicative(function(a, b)
		return a % b
	end, { value.prim_number_type, value.prim_number_type }, { value.prim_number_type }),
	neg = exprs.primitive_applicative(function(a)
		return -a
	end, { value.prim_number_type }, { value.prim_number_type }),

	--["<"] = evaluator.primitive_applicative(function(args)
	--  return { variant = (args[1] < args[2]) and 1 or 0, arg = types.unit_val }
	--end, types.tuple {types.number, types.number}, types.cotuple({types.unit, types.unit})),
	--["=="] = evaluator.primitive_applicative(function(args)
	--  return { variant = (args[1] == args[2]) and 1 or 0, arg = types.unit_val }
	--end, types.tuple {types.number, types.number}, types.cotuple({types.unit, types.unit})),

	--["do"] = evaluator.primitive_operative(do_block),
	let = exprs.primitive_operative(let_bind, "let_bind"),
	record = exprs.primitive_operative(record_build, "record_build"),
	intrinsic = exprs.primitive_operative(intrinsic, "intrinsic"),
	["prim-number"] = lit_term(value.prim_number_type, value.prim_type_type),
	["prim-type"] = lit_term(value.prim_type_type, value.star(1)),
	["prim-func-type"] = exprs.primitive_operative(prim_func_type_impl, "prim_func_type_impl"),
	type = lit_term(value.star(0), value.star(1)),
	type_ = exprs.primitive_operative(startype_impl, "startype_impl"),
	["forall"] = exprs.primitive_operative(forall_type_impl, "forall_type_impl"),
	lambda = exprs.primitive_operative(lambda_impl, "lambda_impl"),
	lambda_implicit = exprs.primitive_operative(lambda_impl_implicit, "lambda_impl_implicit"),
	the = exprs.primitive_operative(the_operative_impl, "the"),
	apply = exprs.primitive_operative(apply_operative_impl, "apply"),
	wrap = build_wrap(typed.prim_wrap, typed.prim_wrapped_type),
	["unstrict-wrap"] = build_wrap(typed.prim_unstrict_wrap, typed.prim_unstrict_wrapped_type),
	wrapped = build_wrapped(typed.prim_wrapped_type),
	["unstrict-wrapped"] = build_wrapped(typed.prim_unstrict_wrapped_type),
	unwrap = build_unwrap(typed.prim_unwrap, typed.prim_wrapped_type),
	["unstrict-unwrap"] = build_unwrap(typed.prim_unstrict_unwrap, typed.prim_unstrict_wrapped_type),
	--["dump-env"] = evaluator.primitive_operative(function(syntax, env) print(environment.dump_env(env)); return true, types.unit_val, env end),
	--["basic-fn"] = evaluator.primitive_operative(basic_fn),
	--tuple = evaluator.primitive_operative(tuple_type_impl),
	--["tuple-of"] = evaluator.primitive_operative(tuple_of_impl),
	--number = { type = types.type, val = types.number }
}

-- FIXME: use these once reimplemented with terms
--local modules = require './modules'
--local cotuple = require './cotuple'

local function create()
	local env = environment.new_env {
		nonlocals = treemap.build(core_operations),
	}
	-- p(env)
	-- p(modules.mod)
	--env = modules.use_mod(modules.module_mod, env)
	--env = modules.use_mod(cotuple.cotuple_module, env)
	-- p(env)
	return env
end

return {
	create = create,
}
