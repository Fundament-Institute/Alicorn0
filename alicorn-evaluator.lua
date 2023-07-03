
local metalanguage = require './metalanguage'
-- local conexpr = require './contextual-exprs'
local types = require './typesystem'

local p = require 'pretty-print'.prettyPrint

local semantic_error_mt = {
  __tostring = function(self)
    local message = self.text
    if self.cause then
      message = message .. " because:\n" .. tostring(self.cause)
    end
    return message
  end
}

local semantic_error = {
  function_args_mismatch = function(cause)
    return {
      text = "function args mismatch",
      cause = cause
    }
  end,
  non_operable_combiner = function(t)
    return {
      text = "value in combiner slot that can't operate of type " .. types.type_name(t)
    }
  end
}

for k, v in pairs(semantic_error) do
  semantic_error[k] = function(...) return setmetatable(v(...), semantic_error_mt) end
end

local evaluates

local operate_behavior = {}

local function evaluate_pairhandler(env, a, b)
  local ok, combiner, env = a:match({evaluates(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)
  if not ok then return false, combiner end
  if not operate_behavior[combiner.type.kind] then return false, semantic_error.non_operable_combiner(combiner.type) end
  return operate_behavior[combiner.type.kind](combiner, b, env)
end
local function evaluate_symbolhandler(env, name)
  --print("looking up symbol", name)
  --p(env)
  local ok, val = env:get(name)
  return ok, val, env
end
local function evaluate_valuehandler(env, val)
  return true, val, env
end

evaluates =
  metalanguage.reducer(
    function(syntax, _, environment)
      -- print('trying to evaluate', syntax)
      return syntax:match(
        {
          metalanguage.ispair(evaluate_pairhandler),
          metalanguage.issymbol(evaluate_symbolhandler),
          metalanguage.isvalue(evaluate_valuehandler)
        },
        metalanguage.failure_handler,
        environment
      )
    end,
    "evaluates"
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

operate_behavior[types.primop_kind] = function(self, ops, env)
  -- print("evaluating operative")
  -- p(self)
  -- p(ops)
  -- p(env)
  return self.val(ops, env)
end

local function primitive_operative(fn)
  return {
    type = types.primop,
    val = fn
  }
end

local function collect_tuple_pair_handler(env, a, b)
  local ok, val, env = a:match({evaluates(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)
  if not ok then return false, val end
  return true, true, val, b, env
end

local function collect_tuple_nil_handler(env) return true, false, nil, nil, env end

local collect_tuple = metalanguage.reducer(function(syntax, _, env)
    local vals = {}
    local ok, continue = true, true
    while ok and continue do
      ok, continue, vals[#vals + 1], syntax, env = syntax:match(
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
end, "collect_tuple")

local evaluates_args = metalanguage.reducer(function(syntax, _, env)
    local vals = {}
    local ok, continue = true, true
    while ok and continue do
      ok, continue, vals[#vals + 1], syntax, env = syntax:match(
        {
          metalanguage.ispair(collect_tuple_pair_handler),
          metalanguage.isnil(collect_tuple_nil_handler)
        },
        metalanguage.failure_handler,
        env
      )
    end
    if not ok then return false, continue end
    return true, vals, env
end, "evaluates_args")

local block = metalanguage.reducer(function(syntax, _, env)
    local lastval, newval
    local ok, continue = true, true
    while ok and continue do
      ok, continue, newval, syntax, env = syntax:match(
        {
          metalanguage.ispair(collect_tuple_pair_handler),
          metalanguage.isnil(collect_tuple_nil_handler)
        },
        metalanguage.failure_handler,
        env
      )
      if ok and continue then lastval = newval end
    end
    if not ok then return false, continue end
    return true, lastval, env
end, "block")

local function primitive_apply(self, operands, environment)
  local ok, args, env = operands:match(
    {
      collect_tuple(metalanguage.accept_handler, environment)
    },
    metalanguage.failure_handler,
    nil
  )
  if not ok then return false, args end
  local ok, err = types.typeident(self.type.params[1], args.type)
  if not ok then return false, semantic_error.function_args_mismatch(err) end
  local res = self.val(args.val)
  return true, {val = res, type = self.type.params[2]}, env
end

operate_behavior[types.primap_kind] = primitive_apply

local function define_operate(kind, handler)
  operate_behavior[kind] = handler
end

local function primitive_applicative(fn, params, results)
  return {type = types.primap(params, results), val = fn}
end


local function eval(syntax, environment)
  return syntax:match({evaluates(metalanguage.accept_handler, environment)}, metalanguage.failure_handler, nil)
end
local function eval_block(syntax, environment)
  return syntax:match({block(metalanguage.accept_handler, environment)}, metalanguage.failure_handler, nil)
end

return {
  evaluates = evaluates,
  -- constexpr = constexpr
  block = block,
  primitive_operative = primitive_operative,
  primitive_applicative = primitive_applicative,
  define_operate = define_operate,
  collect_tuple = collect_tuple,
  evaluates_args = evaluates_args,
  eval = eval,
  eval_block = eval_block
}
