local types = require "typesystem"
local modules = require "modules"
local evaluator = require "alicorn-evaluator"
local metalanguage = require "metalanguage"
local utils = require "reducer-utils"

local function cotuple_construct(t, idx, val)
	if t.kind == types.cotuple_kind then
		if idx < 0 or idx >= #t.params then
			return false, "variant index out of bounds"
		end
		local ok, err = types.typeident(t.params[idx + 1], val.type)
		if not ok then
			return ok, err
		end
		local res = { variant = idx, arg = val.val }
		return true, { type = t, val = res }
	end
	return false, "cotuple construction must only be on cotuple kinds"
end

local function new_cotuple_op_impl(syntax, env)
	local ok, cotuple_type_syntax, constructor_syntax = syntax:match({
		metalanguage.ispair(metalanguage.accept_handler),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, cotuple_type_syntax
	end
	local ok, cotuple_type_val, env = cotuple_type_syntax:match({
		evaluator.evaluates(metalanguage.accept_handler, env),
	}, metalanguage.failure_handler, nil)
	if cotuple_type_val.type ~= types.type then
		return false, "first argument of cotuple construction must evaluate to a type"
	end
	local cotuple_type = cotuple_type_val.val
	if cotuple_type.kind ~= types.cotuple_kind then
		return false, "the first argument of cotuple construction must evaluate to a cotuple type"
	end
	if not ok then
		return ok, cotuple_type
	end
	local ok, constructor_idx_val, constructor_arg = constructor_syntax:match({
		metalanguage.listmatch(
			metalanguage.accept_handler,
			metalanguage.isvalue(metalanguage.accept_handler),
			evaluator.evaluates(utils.accept_with_env, env)
		),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, constructor_idx_val
	end
	if constructor_idx_val.type ~= types.number then
		return false, "cotuple construction variant must be an integer"
	end
	local constructor_idx = constructor_idx_val.val
	local t = cotuple_type.params[constructor_idx + 1]
	local ok, err = types.typeident(t, constructor_arg.val.type)
	if not ok then
		return ok, err
	end
	local val = { variant = constructor_idx, arg = constructor_arg.val.val }
	return true, { type = cotuple_type, val = val }, constructor_arg.env
end

local function cotuple_type_impl(syntax, env)
	local ok, typeargs, env = syntax:match({
		evaluator.collect_tuple(metalanguage.accept_handler, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, typeargs
	end
	for i, t in ipairs(typeargs.type.params) do
		if t ~= types.type then
			return false, "Cotuple-type was provided something that wasn't a type"
		end
	end
	return true, { type = types.type, val = types.cotuple(typeargs.val) }, env
end

local function cotuple_dispatch_impl(syntax, env)
	local ok, subject_eval, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, evaluator.evaluates(utils.accept_with_env, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, subject_eval
	end
	local subject, env = subject_eval.val, subject_eval.env
	if subject.type.kind ~= types.cotuple_kind then
		return false, "dispatch subject must be a cotuple"
	end
	local clause = nil
	-- skip clauses until the relevant one
	-- TODO: check that there aren't too many clauses?
	for i = 0, subject.val.variant do
		ok, clause, tail = tail:match({
			metalanguage.ispair(metalanguage.accept_handler),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, clause
		end
	end
	local ok, name, tail = clause:match({
		metalanguage.listtail(metalanguage.accept_handler, metalanguage.issymbol(metalanguage.accept_handler)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, name
	end
	-- create child scope
	local childenv = env:child_scope()
	-- bind local inchild scope
	ok, childenv =
		childenv:bind_local(name, { val = subject.val.arg, type = subject.type.params[subject.val.variant + 1] })
	if not ok then
		return false, childenv
	end
	-- eval consequent in child scope
	local ok, val, childenv = tail:match({
		evaluator.block(metalanguage.accept_handler, childenv),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, val
	end
	-- exit child scope with result of evaluation
	return ok, val, env:exit_child_scope(childenv)
end

local function cotuple_flow_impl(syntax, env)
	-- note that it's incorrect to directly re-use
	-- cotuple_dispatch_impl for this because it would
	-- re-evaluate the subject every loop.
	-- but maybe shared behavior can be factored out
	local ok, subject_eval, tail = syntax:match({
		metalanguage.listtail(metalanguage.accept_handler, evaluator.evaluates(utils.accept_with_env, env)),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, subject_eval
	end
	local subject, env = subject_eval.val, subject_eval.env
	if subject.type.kind ~= types.cotuple_kind then
		return false, "flow subject must be a cotuple"
	end
	local clause, clauses = nil, {}
	-- read all the clauses
	-- not strictly necessary but reduces re-parsing when looping
	-- every loop is re-interpreted though
	for i = 1, #subject.type.params - 1 do
		ok, clause, tail = tail:match({
			metalanguage.ispair(metalanguage.accept_handler),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, clause
		end
		local ok, name, block = clause:match({
			metalanguage.listtail(metalanguage.accept_handler, metalanguage.issymbol(metalanguage.accept_handler)),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, name
		end
		clauses[#clauses + 1] = { name = name, block = block }
	end
	-- make sure this is the end
	local ok, err = tail:match({
		metalanguage.isnil(metalanguage.accept_handler),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return ok, err
	end
	-- flow time!
	while subject.val.variant ~= 0 do
		local name, block = clauses[subject.val.variant].name, clauses[subject.val.variant].block
		local childenv = env:child_scope()
		ok, childenv = childenv:bind_local(name, {
			val = subject.val.arg,
			type = subject.type.params[subject.val.variant + 1],
		})
		if not ok then
			return false, childenv
		end
		local ok, new_subject, childenv = block:match({
			evaluator.block(metalanguage.accept_handler, childenv),
		}, metalanguage.failure_handler, nil)
		if not ok then
			return ok, new_subject
		end
		env = env:exit_child_scope(childenv)
		if not types.typeident(new_subject.type, subject.type) then
			return false, "flow returns must be consistent"
		end
		subject = new_subject
	end
	return true, {
		val = subject.val.arg,
		type = subject.type.params[1],
	}, env
end

local cotuple_module = modules.build_mod {
	["cotuple-construct"] = evaluator.primitive_operative(new_cotuple_op_impl),
	["cotuple-type"] = evaluator.primitive_operative(cotuple_type_impl),
	["cotuple-dispatch"] = evaluator.primitive_operative(cotuple_dispatch_impl),
	["cotuple-flow"] = evaluator.primitive_operative(cotuple_flow_impl),
}

return {
	cotuple_construct = cotuple_construct,
	cotuple_module = cotuple_module.val,
}
