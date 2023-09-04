-- get new version of let and do working with terms

local metalanguage = require './metalanguage'
-- local conexpr = require './contextual-exprs'
local types = require './typesystem'
local gen = require './terms-generators'
local terms = require './terms'
local evaluator = require './evaluator'

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

local inferred_expression
local checked_expression
local inferred_collect_tuple

local function inferred_expression_pairhandler(env, a, b)
  -- resolve first of the pair as an expression
  -- typecheck it
  -- check type to see how it should be combined
  -- either
  --   resolve rest of the pair as collect tuple
  --   pass it into the operative's arguments
  local ok, combiner, env = a:match({inferred_expression(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)
  if not ok then return false, combiner end

  -- combiner was an evaluated typed value, now it isn't
  local type_of_term, usage_count, term = evaluator.infer(combiner, env.typechecking_context)

  local ok, as_operative = type_of_term:as_operative_type()
  if ok then
    -- FIXME: this doesn't exist yet and API might change
    -- operative input: env, syntax tree, target type
    local operative_result_val = terms.apply_value(as_operative.closure, terms.values.operative_input(env, terms.values.syntax(b), nil))
    -- result should be able to be an inferred term, can fail
    if operative_result_val.kind ~= "value_data" then
      return false, "applying operative did not result in value_data type, typechecker or lua operative mistake when applying at " .. a.anchor .. " to the args at " .. b.anchor
    end
    if operative_result_val.variant == "error" then
      return false, semantic_error.operative_apply_failed(operative_result_val.data, a.anchor, b.anchor)
    end
    -- FIXME: assert type is an inferrable term using new API once it exists
    local resulting_type, usage_counts, term = evaluator.infer(env, operative_result_val.data)
    return terms.inferrable_term.typed(resulting_type, usage_counts, term)
  end

  local ok, as_pi_type = type_of_term:as_pi_type()
  if ok then
    -- multiple quantity of usages in tuple with usage in function arguments
    local ok, tuple, env = b:match({inferred_collect_tuple(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)

    if not ok then
      return false, tuple, env
    end

    return terms.inferrable_term.application(terms.inferrable_term.typed(type_of_term, usage_count, term), tuple)
  end

  local ok = type_of_term.as_prim_function_type()
  if ok then
    --TODO
  end

  return false, "unknown type for pairhandler", env
end

local function inferred_expression_symbolhandler(env, name)
  --print("looking up symbol", name)
  --p(env)
  local ok, val = env:get(name)
  return ok, val, env
end

local function inferred_expression_valuehandler(env, val)
  if val.type == "f64" then
    p(val)
    return true, terms.inferrable_term.typed(terms.value.number_type, gen.declare_array(gen.builtin_number)(), terms.typed_term.literal(terms.value.number(val.val))), env
  end
  p("valuehandler error", val)
  error("unknown value type " .. val.type)
end

-- expression gets split into checked expressions and inferred expressions
local function checked_expression_pairhandler(env, target_type, a, b)
  error("NYI copy from inferred_expression_pairhandler and change to be checked")
end

local function checked_expression_symbolhandler(env, target_type, name)
  --print("looking up symbol", name)
  --p(env)
  local ok, term = inferred_expression_valuehandler(env, val)
  if not ok then
    return false, term, env
  end
  return true, terms.checkable.inferred(term), env
end

local function checked_expression_valuehandler(env, target_type, val)
  local ok, term = checked_expression_valuehandler(env, val)
  if not ok then
    return false, term
  end

  return true, terms.checkable.inferred(term), env
end

inferred_expression =
  metalanguage.reducer(
    function(syntax, _, environment)
      -- print('trying to expression', syntax)
      return syntax:match(
        {
          metalanguage.ispair(inferred_expression_pairhandler),
          metalanguage.issymbol(inferred_expression_symbolhandler),
          metalanguage.isvalue(inferred_expression_valuehandler)
        },
        metalanguage.failure_handler,
        environment
      )
    end,
    "expressions"
  )


checked_expression =
  metalanguage.reducer(
    function(syntax, _, environment)
      -- print('trying to expression', syntax)
      return syntax:match(
        {
          metalanguage.ispair(checked_expression_pairhandler),
          metalanguage.issymbol(checked_expression_symbolhandler),
          metalanguage.isvalue(checked_expression_valuehandler)
        },
        metalanguage.failure_handler,
        environment
      )
    end,
    "expressions"
  )

-- local constexpr =
--   metalanguage.reducer(
--     function(syntax, environment)
--       local ok, val =
--         syntax:match({expressions(metalanguage.accept_handler, environment)}, metalanguage.failure_handler, nil)
--       if not ok then return false, val end
--       return val:asconstant()
--     enfoundendd
--   )

-- operate_behavior[types.primop_kind] = function(self, ops, env)
--   -- print("evaluating operative")
--   -- p(self)
--   -- p(ops)
--   -- p(env)
--   return self.val(ops, env)
-- end

local function primitive_operative(fn)
  return {
    type = types.primop,
    val = fn
  }
end

local function inferred_collect_tuple_pair_handler(env, a, b)
  local ok, val, env = a:match({inferred_expression(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)
  if not ok then return false, val end
  return true, true, val, b, env
end

local function inferred_collect_tuple_nil_handler(env) return true, false, nil, nil, env end

inferred_collect_tuple = metalanguage.reducer(function(syntax, _, env)
    local collected_terms = gen.declare_array(terms.inferrable_term)()
    local ok, continue, next_term = true, true, nil
    while ok and continue do
      ok, continue, next_term, syntax, env = syntax:match(
        {
          metalanguage.ispair(inferred_collect_tuple_pair_handler),
          metalanguage.isnil(inferred_collect_tuple_nil_handler)
        },
        metalanguage.failure_handler,
        env
      )
      if ok and continue then
        collected_terms:append(next_term)
      end
    end
    if not ok then return false, continue end
    return true, terms.inferred.tuple_cons(collected_terms), env
end, "inferred_collect_tuple")

local expressions_args = metalanguage.reducer(function(syntax, _, env)
    local vals = {}
    local ok, continue = true, true
    while ok and continue do
      ok, continue, vals[#vals + 1], syntax, env = syntax:match(
        {
          metalanguage.ispair(inferred_collect_tuple_pair_handler),
          metalanguage.isnil(inferred_collect_tuple_nil_handler)
        },
        metalanguage.failure_handler,
        env
      )
    end
    if not ok then return false, continue end
    return true, vals, env
end, "expressions_args")

local block = metalanguage.reducer(function(syntax, _, env)
    local lastval, newval
    local ok, continue = true, true
    while ok and continue do
      ok, continue, newval, syntax, env = syntax:match(
        {
          metalanguage.ispair(inferred_collect_tuple_pair_handler),
          metalanguage.isnil(inferred_collect_tuple_nil_handler)
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

-- operate_behavior[types.primap_kind] = primitive_apply

-- local function define_operate(kind, handler)
--   operate_behavior[kind] = handler
-- end

local function primitive_applicative(fn, params, results)
  return {type = types.primap(params, results), val = fn}
end


local function eval(syntax, environment)
  return syntax:match({inferred_expression(metalanguage.accept_handler, environment)}, metalanguage.failure_handler, nil)
end
local function eval_block(syntax, environment)
  return syntax:match({block(metalanguage.accept_handler, environment)}, metalanguage.failure_handler, nil)
end

return {
  checked_expression = checked_expression,
  inferred_expression = inferred_expression,
  -- constexpr = constexpr
  block = block,
  primitive_operative = primitive_operative,
  primitive_applicative = primitive_applicative,
  define_operate = define_operate,
  collect_tuple = collect_tuple,
  expressions_args = expressions_args,
  eval = eval,
  eval_block = eval_block
}
