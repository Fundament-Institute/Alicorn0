
local metalanguage = require './metalanguage'
local conexpr = require './contextual-exprs'

local evaluates

local function evaluate_pairhandler(a, b, env)
  local ok, combiner = a:match({evaluates(metalanguage.accept_handler)}, metalanguage.failure_handler, nil)
  if not ok then return false, combiner end
  error "NYI evaluating a pair"
  if combiner.kind == "" then
  end
end
local function evaluate_symbolhandler(name, env)
  return env:get(name)
end
local function evaluate_valuehandler(val, env)
  return true, val
end

evaluates =
  metalanguage.reducer(
    function(syntax, environment)
      return syntax:match(
        {
          metalanguage.ispair(evaluate_pairhandler),
          metalanguage.issymbol(evaluate_symbolhandler),
          metalanguage.isvalue(evaluate_valuehandler)
        },
        metalanguage.failure_handler,
        environment
      )
    end
  )

local constexpr =
  metalanguage.reducer(
    function(syntax, environment)
      local ok, val =
        syntax:match({evaluates(metalanguage.accept_handler, environment)}, metalanguage.failure_handler, nil)
      if not ok then return false, val end
      return val:asconstant()
    end
  )


return {
  evaluates = evaluates,
  constexpr = constexpr
}
