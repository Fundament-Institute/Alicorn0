
local metalanguage = require './metalanguage'
-- local conexpr = require './contextual-exprs'
local types = require './typesystem'


local evaluates

local function evaluate_pairhandler(a, b, env)
  local ok, combiner, env = a:match({evaluates(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)
  if not ok then return false, combiner end
  return combiner:apply(b, env)
end
local function evaluate_symbolhandler(name, env)
  local ok, val = env:get(name)
  return ok, val, env
end
local function evaluate_valuehandler(val, env)
  return true, val, env
end

evaluates =
  metalanguage.reducer(
    function(syntax, environment)
      print('trying to evaluate', syntax)
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

-- local constexpr =
--   metalanguage.reducer(
--     function(syntax, environment)
--       local ok, val =
--         syntax:match({evaluates(metalanguage.accept_handler, environment)}, metalanguage.failure_handler, nil)
--       if not ok then return false, val end
--       return val:asconstant()
--     enfoundendd
--   )


local function primitive_operative(fn)
  return {
    type = types.primop,
    apply = fn
  }
end

local function collect_tuple_pair_handler(a, b, env)
  local ok, val, env = a:match({evaluates(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)
  return true, true, val, b, env
end

local function collect_tuple_nil_handler(env) return true, false, nil, env end

local collect_tuple = metalanguage.reducer(function(syntax, env)
    local vals = {}
    local ok, continue = true, true
    while ok and continue do
      ok, continue, vals[#vals], env = syntax:match(
        {
          metalanguage.ispair(collect_tuple_pair_handler),
          metalanguage.isnil(collect_tuple_nil_handler)
        },
        metalanguage.failure_handler,
        env
      )
    end
    if not ok then return false, continue end
    local tuple_val, tuple_t_args = {}, {}
    for i, v in ipairs(vals) do
      tuple_val[i] = v.val
      tuple_t_args[i] = v.type
    end
    local tuple_t = types.tuple(tuple_t_args)
    return true, {val = tuple_val, type = tuple_t}, env
end)

local function primitive_apply(self, operands, environment)
  local ok, args, env = operands:match(
    {
      collect_tuple(metalanguage.accept_handler)
    },
    metalanguage.failure_handler,
    environment
  )
  if not ok then return false, args end
  local ok, err = types.typeident(self.type.params[1], args.type)
  if not ok then return false, err end
  local res = self.fn(args.val)
  return {val = res, type = self.type.params[2]}
end


local function primitive_applicative(fn, params, results)
  return {type = types.primap(params, results), fn = fn, apply = primitive_apply}
end


local function eval(syntax, environment)
  return syntax:match({evaluates(metalanguage.accept_handler, environment)}, metalanguage.failure_handler, nil)
end

return {
  evaluates = evaluates,
  -- constexpr = constexpr
  primitive_operative = primitive_operative,
  primitive_applicative = primitive_applicative,
  collect_tuple = collect_tuple,
  eval = eval
}
