local types = require "./typesystem"
local evaluator = require "./alicorn-evaluator"
local environment = require "./environment"
local metalang = require "./metalanguage"
local treemap = require "./lazy-prefix-tree"

local module_type = {
	kind = {
		kind_name = "module_kind",
		type_name = function()
			return "module"
		end,
		duplicable = function()
			return true
		end,
		discardable = function()
			return true
		end,
	},
	params = {},
}

local function module_retain(binding)
	if binding.kind == "reusable" then
		return true, binding
	else
		return false
	end
end

local function new_mod(values)
	local self = {
		values = values:filtermap_values(module_retain),
	}
	if self.values == nil then
		error "tried to new_mod something that becomes nil"
	end
	return { type = module_type, val = self }
end

local function index_mod(mod, name)
	return mod.values:get(name)
end

local function use_mod(mod, env)
	-- print "in use_mod"
	-- p(mod)
	return environment.new_env {
		locals = env.locals,
		nonlocals = env.nonlocals:extend(mod.values),
		carrier = env.carrier,
		perms = env.perms,
	}
end

local function open_mod(mod, env)
	return environment.new_env {
		locals = env.locals:extend(mod.values),
		nonlocals = env.nonlocals,
		carrier = env.carrier,
		perms = env.perms,
	}
end

local function use_mod_op_impl(syntax, env)
	local ok, modval, env = syntax:match({
		evaluator.evaluates_args(metalang.accept_handler, env),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, modval
	end
	if #modval ~= 1 or modval[1].type ~= module_type then
		return false, "using syntax should take exactly one argument, a module"
	end
	return true, types.unit_val, use_mod(modval[1].val, env)
end

local function open_mod_op_impl(syntax, env)
	local ok, modval, env = syntax:match({
		evaluator.evaluates_args(metalang.accept_handler, env),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, modval
	end
	if #modval ~= 1 or modval[1].type ~= module_type then
		return false, "open-mod syntax should take exactly one argument, a module"
	end
	return true, types.unit_val, open_mod(modval[1].val, env)
end

local function get_op_impl(syntax, env)
	local ok, modval, env, name = syntax:match({
		metalang.listmatch(
			metalang.accept_handler,
			{ evaluator.evaluates(metalang.accept_handler, env), metalang.issymbol(metalang.accept_handler) }
		),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, modval
	end
	print("module get", ok, modval, env, name)
	if not modval.type == module_type then
		return false, "first argument of module get must be a module"
	end
	return true, index_mod(modval.val)
end

local function mod_op_impl(syntax, env)
	local childenv = env:child_scope()
	local ok, val, childenv = syntax:match({
		evaluator.block(metalang.accept_handler, childenv),
	}, metalang.failure_handler, nil)
	if not ok then
		return ok, val
	end
	local mod = new_mod(childenv.locals)
	env = env:exit_child_scope(childenv)
	return true, mod, env
end

local function build_mod(tab)
	local tmp = {}
	for k, v in pairs(tab) do
		tmp[k] = { kind = "reusable", val = v }
	end
	local val = { values = treemap.build(tmp) }
	if val.values == nil then
		error "tried to build a module that went to nil"
	end
	return { type = module_type, val = val }
end

local mod_mod = build_mod {
	module = evaluator.primitive_operative(mod_op_impl),
	get = evaluator.primitive_operative(get_op_impl),
	["use-mod"] = evaluator.primitive_operative(use_mod_op_impl),
	["open-mod"] = evaluator.primitive_operative(open_mod_op_impl),
}

return {
	new_mod = new_mod,
	index_mod = index_mod,
	use_mod = use_mod,
	open_mod = open_mod,
	build_mod = build_mod,
	module_mod = mod_mod.val,
	module = mod_mod.val,
}
