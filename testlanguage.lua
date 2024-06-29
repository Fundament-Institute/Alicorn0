local metalang = require "./metalanguage"

local eval

local function eval_passhandler(env, val)
	--print("eval pass handler", val, env)
	return true, val, env
end

local eval

local function Eval(syntax, matcher, environment)
	return eval(syntax, environment)
end

local evaluates = metalang.reducer(Eval, "evaluates")

local function eval_pairhandler(env, a, b)
	--print("in eval pairhandler", a, b, env)
	local ok, combiner, _ = a:match({
		evaluates(eval_passhandler, env),
	}, metalang.failure_handler, env)
	if not ok then
		return false, combiner
	end
	local ok, val, newenv = combiner:apply(b, env)
	--print("eval pair", ok, val, newenv)
	return ok, val, newenv
end

local function symbolenvhandler(env, name)
	--print("symbolenvhandler(", name, env, ")")
	local res = env:get(name)
	if res ~= nil then
		return true, res
	else
		return false, "environment does not contain a binding for " .. name
	end
end

local function SymbolInEnvironment(syntax, environment)
	--print("in symbol in environment reducer", matcher.kind, matcher[1], matcher)
	return syntax:match({
		metalang.issymbol(symbolenvhandler),
	}, metalang.failure_handler, environment)
end

local symbol_in_environment = metalang.reducer(SymbolInEnvironment, "symbol in env")

function eval(syntax, environment)
	return syntax:match({
		symbol_in_environment(eval_passhandler, environment),
		metalang.isvalue(eval_passhandler),
		metalang.ispair(eval_pairhandler),
	}, metalang.failure_handler, environment)
end

local function syntax_args_val_handler(_, val, newenv)
	return true, val, newenv
end

local function syntax_args_nil_handler(data)
	return true, false
end

local function syntax_args_pair_handler(env, a, b)
	local ok, val, _ = a:match({
		evaluates(syntax_args_val_handler, env),
	}, metalang.failure_handler, nil)
	--print("args pair handler", ok, val, _, b)
	return true, true, val, b
end

local function EvalArgs(syntax, matcher, environment)
	local args = {}
	local ok, ispair, val, tail = true, true, nil, nil
	while ok and ispair do
		ok, ispair, val, tail = syntax:match({
			metalang.ispair(syntax_args_pair_handler),
			metalang.isnil(syntax_args_nil_handler),
		}, metalang.failure_handler, environment)
		if not ok then
			return false, ispair
		end
		if ispair then
			args[#args + 1] = val
			syntax = tail
		end
	end
	return true, args
end

local evalargs = metalang.reducer(EvalArgs, "evalargs")

local primitive_applicative_mt = {
	__index = {
		apply = function(self, ops, env)
			local ok, args = ops:match({
				evalargs(metalang.accept_handler, env),
			}, metalang.failure_handler, nil)
			local res = self.fn(table.unpack(args))
			return true, metalang.value(res), env
		end,
	},
}

local function primitive_applicative(fn)
	return setmetatable({ fn = fn }, primitive_applicative_mt)
end

local primitive_operative_mt = {
	__index = {
		apply = function(self, ops, env)
			return self.fn(ops, env)
		end,
	},
}

local function primitive_operative(fn)
	return setmetatable({ fn = fn }, primitive_operative_mt)
end

return {
	eval = eval,
	evalargs = evalargs,
	evaluates = evaluates,
	primitive_applicative = primitive_applicative,
	primitive_operative = primitive_operative,
}
