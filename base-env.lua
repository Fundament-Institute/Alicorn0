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

	local env = bind.env

	if type(name) == "table" then
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
	local str = str_env.val
	local ok, type, env = syntax:match({
		metalang.listmatch(metalang.accept_handler, exprs.inferred_expression(metalang.accept_handler, env)),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, type
	end
	return true, terms.inferrable_term.prim_intrinsic(str, type), env
end

local basic_fn_kind = {
	kind_name = "basic_fn_kind",
	type_name = function()
		return "basic_fn"
	end,
	duplicable = function()
		return true
	end,
	discardable = function()
		return true
	end,
}

local basic_fn_type = { kind = basic_fn_kind, params = {} }

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
	local env, val = type_env.env:exit_block(type_env.val, shadowed)
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
	
	local function build_type_term(args)
		return
			terms.inferrable_term.qtype(
				terms.inferrable_term.typed(
					terms.value.quantity_type,
					usage_array(),
					terms.typed_term.literal(
						terms.value.quantity(terms.quantity.unrestricted))),
				terms.inferrable_term.tuple_type(args)
			)
	end

	local names = gen.declare_array(gen.builtin_string)()
	print("is env an environment? (before loop)")
	--p(env)
	print(env.get)
	print(env.enter_block)

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
	env = env:bind_local(terms.binding.tuple_elim(names, build_type_term(args)))
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

		syntax = tail
	end
	if not ok then
		return false, continue
	end

	local fn_type_term = terms.value.qtype(terms.quantity.unrestricted, terms.value.prim_function_type(args, results))
	
	return true, fn_type_term, env
end, "prim_func_type_impl")

-- TODO: abstract so can reuse for func type and prim func type
local function prim_func_type_impl(syntax, env)
	print("in prim_func_type_impl")
	local result =
		syntax:match({ prim_func_type_impl_reducer(metalang.accept_handler, env) }, metalang.failure_handler, env)
	p(result)
	error "NYI"
	-- parse sequence of ascribed names, arrow, then sequence of ascribed names
	-- for each ascribed name:
	-- enter a block, perform lambda binding, perform tuple destrucutring binding, parse out the type of the ascription

	--local ok,
end

local value = terms.value

local usage_array = gen.declare_array(gen.builtin_number)
local function lit_term(val, typ)
	return terms.inferrable_term.typed(typ, usage_array(), terms.typed_term.literal(val))
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
	let = exprs.primitive_operative(let_bind),
	record = exprs.primitive_operative(record_build),
	intrinsic = exprs.primitive_operative(intrinsic),
	["prim-number"] = lit_term(value.prim_number_type, value.prim_type_type),
	["prim-func-type"] = exprs.primitive_operative(prim_func_type_impl),
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
