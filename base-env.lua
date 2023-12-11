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
	local ok, name, bind = syntax:match({
		metalang.listmatch(
			metalang.accept_handler,
			metalang.oneof(
				metalang.accept_handler,
				metalang.issymbol(metalang.accept_handler),
				metalang.list_many(metalang.accept_handler, metalang.issymbol(metalang.accept_handler))
			),
			metalang.symbol_exact(metalang.accept_handler, "="),
			exprs.inferred_expression(utils.accept_with_env, env)
		),
	}, metalang.failure_handler, nil)

	if not ok then
		return false, name
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
			terms.value.quantity(terms.quantity.unrestricted, terms.unit_type),
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
	return true, terms.inferrable_term.prim_intrinsic(str, type--[[terms.checkable_term.inferrable(type)]]), env
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


local ascribed_name = metalang.reducer(function(syntax, env, prev, names)
	-- print("ascribed_name trying")
	-- p(syntax)
	-- print(prev:pretty_print())
	-- print("is env an environment? (start of ascribed name)")
	-- print(env.get)
	-- print(env.enter_block)
	---@cast env Environment
	local shadowed, env = env:enter_block()
	env = env:bind_local(terms.binding.annotated_lambda("#prev", prev))
	local ok, prev_binding = env:get("#prev")
	if not ok then
		error "#prev should always be bound, was just added"
	end
	env = env:bind_local(terms.binding.tuple_elim(names, prev_binding))
	local ok, name, type_env = syntax:match({
		metalang.listmatch(
			metalang.accept_handler,
			metalang.issymbol(metalang.accept_handler),
			metalang.symbol_exact(metalang.accept_handler, ":"),
			exprs.inferred_expression(utils.accept_with_env, env)
		),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, name
	end
	---@type Environment
	env = type_env.env
	local env, val = env:exit_block(type_env.val, shadowed)
	-- print("is env an environment? (end of ascribed name)")
	-- print(env.get)
	-- print(env.enter_block)
	return true, name, val, env
end, "ascribed_name")

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
	local value_array = gen.declare_array(terms.value)
	local inf_array = gen.declare_array(terms.inferrable_term)
	local usage_array = gen.declare_array(gen.builtin_number)
	local function tup_cons(...)
		return terms.inferrable_term.tuple_cons(inf_array(...))
	end
	local function cons(...)
		return terms.inferrable_term.enum_cons(terms.value.tuple_defn_type, "cons", tup_cons(...))
	end
	local empty = terms.inferrable_term.enum_cons(terms.value.tuple_defn_type, "empty", tup_cons())
	local args = empty

	local unrestricted_term = terms.inferrable_term.typed(
		terms.value.quantity_type,
		usage_array(),
		terms.typed_term.literal(
			terms.value.quantity(terms.quantity.unrestricted)))
	
	local function build_type_term(args)
		return
			terms.inferrable_term.qtype(
				unrestricted_term,
				terms.inferrable_term.tuple_type(args)
			)
	end
	local function build_prim_type_term(args)
		return
			terms.inferrable_term.qtype(
				unrestricted_term,
				terms.inferrable_term.prim_tuple_type(args)
			)
	end

	local names = gen.declare_array(gen.builtin_string)()
	print("is env an environment? (before loop)")
	--p(env)
	print(env.get)
	print(env.enter_block)
	if not env.enter_block then
		error "env isn't an environment in prim_func_type_impl_reducer"
	end

	local head, tail, name, type_val, type_env
	local ok, continue = true, true
	while ok and continue do
		ok, head, tail = syntax:match({ metalang.ispair(metalang.accept_handler) }, metalang.failure_handler, env)
		print(env)
		if not ok then
			break
		end

		print("is env an environment? (in loop)")
		--p(env)
		print(env.get)
		print(env.enter_block)

		print "args in loop is"
		print(args:pretty_print())

		ok, continue, name, type_val, type_env = head:match({
			metalang.symbol_exact(function()
				return true, false
			end, "->"),
			ascribed_name(function(ok, ...)
				return ok, true, ...
			end, env, build_type_term(args), names),
		}, metalang.failure_handler, env)

		if continue then
			-- type_env:bind_local(terms.binding.let(name, type_val))
			-- local arg = nil
			-- args = cons(args, arg)
		end
		if ok and continue then
			env = type_env
			args = cons(args, type_val)
			names = names:copy()
			names:append(name)
		end
		print("arg", ok, continue, name, type_val, type_env)
		--error "TODO use ascribed_name results"

		syntax = tail
	end
	print("moving on to return type")
	ok, continue = true, true
	local shadowed, env = env:enter_block()
	env = env:bind_local(terms.binding.annotated_lambda("#arg", build_type_term(args)))
	local ok, arg = env:get("#arg")
	env = env:bind_local(terms.binding.tuple_elim(names, arg))
	names = gen.declare_array(gen.builtin_string)()
	local results = empty
	while ok and continue do
		ok, head, tail = syntax:match({ metalang.ispair(metalang.accept_handler) }, metalang.failure_handler, env)
		print(env)
		if not ok then
			break
		end

		ok, continue, name, type_val, type_env = head:match({
			metalang.isnil(function()
				return true, false
			end),
			ascribed_name(function(ok, ...)
				return ok, true, ...
			end, env, build_type_term(results), names),
		}, metalang.failure_handler, env)
		print("result", ok, continue, name, type_val, type_env)

		if ok and continue then
			env = type_env
			results = cons(results, type_val)
			names = names:copy()
			names:append(name)
		end

		if not ok then
			return false, continue
		end

		syntax = tail
	end

	local env, fn_res_term = env:exit_block(build_prim_type_term(results), shadowed)
	local fn_type_term = terms.inferrable_term.qtype(unrestricted_term, terms.inferrable_term.prim_function_type(build_prim_type_term(args), fn_res_term))
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
	print("finished matching prim_func_type_impl and got")
	print(fn_type_term:pretty_print())
	if not ok then return ok, fn_type_term end
	if not env.enter_block then
		error "env isn't an environment at end in prim_func_type_impl"
	end
	return ok, fn_type_term, env
	-- parse sequence of ascribed names, arrow, then sequence of ascribed names
	-- for each ascribed name:
	-- enter a block, perform lambda binding, perform tuple destrucutring binding, parse out the type of the ascription

	--local ok,
end

local forall_type_impl_reducer = metalang.reducer(function(syntax, env)
	local value_array = gen.declare_array(terms.value)
	local inf_array = gen.declare_array(terms.inferrable_term)
	local usage_array = gen.declare_array(gen.builtin_number)
	local function tup_cons(...)
		return terms.inferrable_term.tuple_cons(inf_array(...))
	end
	local function cons(...)
		return terms.inferrable_term.enum_cons(terms.value.tuple_defn_type, "cons", tup_cons(...))
	end
	local empty = terms.inferrable_term.enum_cons(terms.value.tuple_defn_type, "empty", tup_cons())
	local args = empty

	local unrestricted_term = terms.inferrable_term.typed(
		terms.value.quantity_type,
		usage_array(),
		terms.typed_term.literal(
			terms.value.quantity(terms.quantity.unrestricted)))
	
	local function build_type_term(args)
		return
			terms.inferrable_term.qtype(
				unrestricted_term,
				terms.inferrable_term.tuple_type(args)
			)
	end

	local names = gen.declare_array(gen.builtin_string)()
	if not env.enter_block then
		error "env isn't an environment in prim_func_type_impl_reducer"
	end

	local head, tail, name, type_val, type_env
	local ok, continue = true, true
	while ok and continue do
		ok, head, tail = syntax:match({ metalang.ispair(metalang.accept_handler) }, metalang.failure_handler, env)
		print(env)
		if not ok then
			break
		end

		if not env or not env.get then
			error "env isn't an environment in prim_func_type_impl_reducer"
		end

		print "args in loop is"
		print(args:pretty_print())

		ok, continue, name, type_val, type_env = head:match({
			metalang.symbol_exact(function()
				return true, false
			end, "->"),
			ascribed_name(function(ok, ...)
				return ok, true, ...
			end, env, build_type_term(args), names),
		}, metalang.failure_handler, env)

		if continue then
			-- type_env:bind_local(terms.binding.let(name, type_val))
			-- local arg = nil
			-- args = cons(args, arg)
		end
		if ok and continue then
			env = type_env
			args = cons(args, type_val)
			names = names:copy()
			names:append(name)
		end
		print("arg", ok, continue, name, type_val, type_env)
		--error "TODO use ascribed_name results"

		syntax = tail
	end
	print("moving on to return type")
	ok, continue = true, true
	local shadowed, env = env:enter_block()
	env = env:bind_local(terms.binding.annotated_lambda("#arg", build_type_term(args)))
	local ok, arg = env:get("#arg")
	env = env:bind_local(terms.binding.tuple_elim(names, arg))
	names = gen.declare_array(gen.builtin_string)()
	local results = empty
	while ok and continue do
		ok, head, tail = syntax:match({ metalang.ispair(metalang.accept_handler) }, metalang.failure_handler, env)
		if not ok then
			break
		end

		ok, continue, name, type_val, type_env = head:match({
			metalang.isnil(function()
				return true, false
			end),
			ascribed_name(function(ok, ...)
				return ok, true, ...
			end, env, build_type_term(results), names),
		}, metalang.failure_handler, env)
		print("result", ok, continue, name, type_val, type_env)

		if ok and continue then
			env = type_env
			results = cons(results, type_val)
			names = names:copy()
			names:append(name)
		end

		if not ok then
			return false, continue
		end

		syntax = tail
	end

	local env, fn_res_term = env:exit_block(build_type_term(results), shadowed)
	local fn_type_term = terms.inferrable_term.qtype(
		unrestricted_term,
		terms.inferrable_term.pi(
			build_type_term(args),
			terms.inferrable_term.typed(
				terms.value.param_info_type,
				usage_array(),
				terms.typed_term.literal(
					terms.value.param_info(
						terms.value.visibility(
							terms.visibility.explicit
						)
					)
				)
			),
			fn_res_term,
			terms.inferrable_term.typed(
				terms.value.result_info_type,
				usage_array(),
				terms.typed_term.literal(
					terms.value.result_info(
						terms.value.purity(
							terms.purity.pure
						)
					)
				)
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
	print("finished matching prim_func_type_impl and got")
	print(fn_type_term:pretty_print())
	if not ok then return ok, fn_type_term end
	if not env.enter_block then
		error "env isn't an environment at end in prim_func_type_impl"
	end
	return ok, fn_type_term, env
	-- parse sequence of ascribed names, arrow, then sequence of ascribed names
	-- for each ascribed name:
	-- enter a block, perform lambda binding, perform tuple destrucutring binding, parse out the type of the ascription

	--local ok,
end

---@param syntax any
---@param env Environment
---@return boolean
---@return unknown
---@return unknown|nil
local function lambda_impl(syntax, env)
	local value_array = gen.declare_array(terms.value)
	local inf_array = gen.declare_array(terms.inferrable_term)
	local usage_array = gen.declare_array(gen.builtin_number)
	local string_array = gen.declare_array(gen.builtin_string)
	local function tup_cons(...)
		return terms.inferrable_term.tuple_cons(inf_array(...))
	end
	local function cons(...)
		return terms.inferrable_term.enum_cons(terms.value.tuple_defn_type, "cons", tup_cons(...))
	end
	local empty = terms.inferrable_term.enum_cons(terms.value.tuple_defn_type, "empty", tup_cons())
	local args = empty

	local unrestricted_term = terms.inferrable_term.typed(
		terms.value.quantity_type,
		usage_array(),
		terms.typed_term.literal(
			terms.value.quantity(terms.quantity.unrestricted)))
	
	local function build_type_term(args)
		return
			terms.inferrable_term.qtype(
				unrestricted_term,
				terms.inferrable_term.tuple_type(args)
			)
	end

	local ok, params_group, tail = syntax:match(
		{
			metalang.listtail(
				function(_, thr, tail, ...)
					return true, {names = thr.names, types = build_type_term(thr.args), env = thr.env}, tail
				end,
				metalang.list_many_threaded(
					function(_, col, thr)
						return true, thr
					end,
					function(thread)
						return ascribed_name(
							function(_, name, typ, env)
								local names = thread.names:copy()
								names:append(name)
								return true, {name = name, type = typ}, {
									names = names,
									args = cons(thread.args, typ),
									env = env
								}
							end,
							thread.env,
							build_type_term(thread.args),
							thread.names
						)
					end, {
					names = string_array(),
					args = empty,
					env = env
				})
			)
		},
		metalang.failure_handler,
		nil
	)
	if not ok then return ok, params_group end

	local shadow, inner_env = env:enter_block()
	inner_env = inner_env:bind_local(terms.binding.annotated_lambda("#arg", params_group.types))
	local _, arg = inner_env:get("#arg")
	inner_env = inner_env:bind_local(terms.binding.tuple_elim(params_group.names, arg))
	local ok, expr, env = tail:match({exprs.block(metalang.accept_handler, exprs.ExpressionArgs.new(terms.expression_target.infer, env))}, metalang.failure_handler, nil)
	if not ok then return ok, expr end
	local resenv, term = env:exit_block(expr, shadow)
	return true, term, resenv
end


local value = terms.value
local typed = terms.typed_term

local usage_array = gen.declare_array(gen.builtin_number)
local val_array = gen.declare_array(value)
local function startype_impl(syntax, env)
	local ok, level_val = syntax:match(
		{
			metalang.listmatch(
				metalang.isvalue(metalang.accept_handler)
			)
		}
	)
	if not ok then return ok, level_val end
	if level_val.type ~= "f64" then
		return false, "literal must be a number for type levels"
	end
	if level_val.val % 1 ~= 0 then
		return false, "literal must be an integer for type levels"
	end
	local term = terms.inferrable_term.typed(
		terms.typed_term.star(level_val.val + 1),
		usage_array(),
		terms.typed_term.star(level_val.val)
	)

	return true, term, env
end

local function lit_term(val, typ)
	return terms.inferrable_term.typed(typ, usage_array(), terms.typed_term.literal(val))
end
local function unrestricted(x)
	return value.qtype(value.quantity(terms.quantity.unrestricted), x)
end

local function val_tup_cons(...)
	return value.tuple_value(val_array(...))
end
local function val_desc_elem(x)
	return value.enum_value("cons", x)
end
local val_desc_empty = value.enum_value("empty", val_tup_cons())

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
	["prim-number"] = lit_term(
		unrestricted(value.prim_number_type),
		unrestricted(value.prim_type_type)),
	["prim-type"] = lit_term(
		unrestricted(value.prim_type_type),
		unrestricted(value.star(1))),
	["prim-func-type"] = exprs.primitive_operative(prim_func_type_impl, "prim_func_type_impl"),
	type = lit_term(value.star(1), value.star(0)),
	type_ = exprs.primitive_operative(startype_impl, "startype_impl"),
	["forall"] = exprs.primitive_operative(forall_type_impl, "forall_type_impl"),
	lambda = exprs.primitive_operative(lambda_impl, "lambda_impl"),
	box = lit_term(
		value.closure(
			typed.tuple_elim(
				typed.bound_variable(1),
				2,
				typed.prim_box(typed.bound_variable(3))
			),
			terms.runtime_context()
		),
		unrestricted(
			value.pi(
				unrestricted(
					value.tuple_type(
						val_desc_elem(
							val_tup_cons(
								val_desc_elem(
									val_tup_cons(
										val_desc_empty,
										value.closure(
											typed.tuple_elim(
												typed.bound_variable(1),
												0,
												typed.qtype(
													typed.literal(value.quantity(terms.quantity.erased)),
													typed.star(1))
											),
											terms.runtime_context()
										)
									)
								),
								value.closure(
									terms.typed_term.tuple_elim(
										terms.typed_term.bound_variable(1),
										1,
										typed.bound_variable(2)
									),
									terms.runtime_context()
								)
							)
						)
					)
				),
				value.param_info(value.visibility(terms.visibility.explicit)),
				value.closure(
					typed.tuple_elim(
						typed.bound_variable(1),
						2,
						typed.qtype(
							typed.literal(value.quantity(terms.quantity.erased)),
							typed.prim_boxed_type(
								typed.bound_variable(2)
							)
						)
					),
					terms.runtime_context()
				),
				value.result_info(terms.result_info(terms.purity.pure))
			)
		)
	),
	unbox = lit_term(
		value.closure(
			typed.tuple_elim(
				typed.bound_variable(1),
				2,
				typed.prim_unbox(typed.bound_variable(3))
			),
			terms.runtime_context()
		),
		unrestricted(
			value.pi(
				unrestricted(
					value.tuple_type(
						val_desc_elem(
							val_tup_cons(
								val_desc_elem(
									val_tup_cons(
										val_desc_empty,
										value.closure(
											typed.tuple_elim(
												typed.bound_variable(1),
												0,
												typed.qtype(
													typed.literal(value.quantity(terms.quantity.erased)),
													typed.star(1))
											),
											terms.runtime_context()
										)
									)
								),
								value.closure(
									terms.typed_term.tuple_elim(
										terms.typed_term.bound_variable(1),
										1,
										typed.qtype(
											typed.literal(value.quantity(terms.quantity.erased)),
											typed.prim_boxed_type(
												typed.bound_variable(2)
											)
										)
									),
									terms.runtime_context()
								)
							)
						)
					)
				),
				value.param_info(value.visibility(terms.visibility.explicit)),
				value.closure(
					typed.tuple_elim(
						typed.bound_variable(1),
						2,
						typed.bound_variable(2)
					),
					terms.runtime_context()
				),
				value.result_info(terms.result_info(terms.purity.pure))
			)
		)
	),
	boxed = lit_term(
		value.closure(
			typed.tuple_elim(
				typed.bound_variable(1),
				1,
				typed.qtype(
					typed.literal(value.quantity(terms.quantity.erased)),
					typed.prim_boxed_type(typed.bound_variable(2))
				)
			),
			terms.runtime_context()
		),
		unrestricted(
			value.pi(
				unrestricted(
					value.tuple_type(
						val_desc_elem(
							val_tup_cons(
								val_desc_empty,
								value.closure(
									typed.tuple_elim(
										typed.bound_variable(1),
										0,
										typed.qtype(
											typed.literal(value.quantity(terms.quantity.erased)),
											typed.star(1))
									),
									terms.runtime_context()
								)
							)
						)
					)
				),
				value.param_info(value.visibility(terms.visibility.explicit)),
				value.closure(
					typed.tuple_elim(
						typed.bound_variable(1),
						1,
						typed.qtype(
							typed.literal(value.quantity(terms.quantity.erased)),
							typed.literal(value.prim_type_type)
						)
					),
					terms.runtime_context()
				),
				value.result_info(terms.result_info(terms.purity.pure))
			)
		)
	),
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
