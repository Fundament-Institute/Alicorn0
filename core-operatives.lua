local metalang = require "./metalanguage"
local alicorn = require "./alicorn-evaluator"
local conexpr = require "./contextual-exprs"
local environment = require "./environment"

local val = metalang.primitive_operative(function(syntax, env)
	local ok, name, expr, nextenv = syntax:match({
		metalang.listmatch(
			metalang.accept_handler,
			metalang.any(
				metalang.listof(metalang.accept_handler, metalang.issymbol(metalang.accept_handler)),
				metalang.issymbol(metalang.accept_handler)
			),
			metalang.symbol_exact(metalang.accept_handler, "="),
			alicorn.evaluates(metalang.accept_handler, env)
		),
	}, metalang.failure_handler, nil)
	if not ok then
		return false, name
	end
	local binder, envres
	if type(name) == "table" then
		binder = conexpr.bindtuple(name)
	elseif type(name) == "string" then
		binder = conexpr.bindval(name)
	else
		error "names had an invalid value?"
	end
end)
