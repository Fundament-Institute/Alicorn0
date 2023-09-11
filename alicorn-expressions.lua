-- get new version of let and do working with terms

local metalanguage = require './metalanguage'
-- local conexpr = require './contextual-exprs'
local types = require './typesystem'

local terms = require './terms'
local runtime_context = terms.runtime_context
local typechecking_context = terms.typechecking_context
local inferrable_term = terms.inferrable_term
local typed_term = terms.typed_term
local quantity = terms.quantity
local visibility = terms.visibility
local purity = terms.purity
local result_info = terms.result_info
local value = terms.value
local prim_syntax_type = terms.prim_syntax_type
local prim_environment_type = terms.prim_environment_type
local prim_inferrable_term_type = terms.prim_inferrable_term_type

local gen = require './terms-generators'
local array = gen.declare_array
local inferrable_array = array(inferrable_term)
local typed_array = array(typed_term)
local value_array = array(value)
local usage_array = array(gen.builtin_number)

local function qtype(q, val) return value.qtype(value.quantity(q), val) end
local function unrestricted(val) return qtype(quantity.unrestricted, val) end
local function linear(val) return qtype(quantity.linear, val) end
local function erased(val) return qtype(quantity.erased, val) end
local param_info_explicit = value.param_info(value.visibility(visibility.explicit))
local param_info_implicit = value.param_info(value.visibility(visibility.implicit))
local result_info_pure = value.result_info(result_info(purity.pure))
local result_info_effectful = value.result_info(result_info(purity.effectful))
local function tup_val(...) return value.tuple_value(value_array(...)) end
local function cons(...) return value.data_value("cons", tup_val(...)) end
local empty = value.data_value("empty", tup_val())

local evaluator = require './evaluator'
local const_combinator = evaluator.const_combinator
local infer = evaluator.infer

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
local inferred_collect_prim_tuple

local infix_data = {
  ["="] = {precedence = 2, associativity = "r"},
  ["|"] = {precedence = 3, associativity = "l"},
  ["&"] = {precedence = 3, associativity = "l"},
  ["!"] = {precedence = 3, associativity = "l"},
  ["<"] = {precedence = 4, associativity = "l"},
  [">"] = {precedence = 4, associativity = "l"},
  ["+"] = {precedence = 5, associativity = "l"},
  ["-"] = {precedence = 5, associativity = "l"},
  ["*"] = {precedence = 6, associativity = "l"},
  ["/"] = {precedence = 6, associativity = "l"},
  ["%"] = {precedence = 6, associativity = "l"},
  ["^"] = {precedence = 7, associativity = "r"},
  [":"] = {precedence = 8, associativity = "l"},
  -- # is the comment character and is forbidden here
}


local function check_infix_expression_handler(dat, a, b)
  local env, prec = dat.env, dat.prec
  local ok, name = a:match(
    {
      metalanguage.is_symbol(metalanguage.accept_handler)
    },
    metalanguage.failure_handler,
    nil
  )
  local data = infix_data[name:sub(1,1)]
  if data then
    local ok, ifx, op, rhs
  end
end

local function inferred_expression_pairhandler(env, a, b)


  local ok, ifx, op, args = b:match(
    {
      metalanguage.is_pair(check_infix_expression_handler)
    },
    metalanguage.failure_handler,
    {env = env, prec = 0, lhs = a}
  )

  local combiner
  if ok and ifx then
    combiner = env:get("_" + op + "_")
  else
    ok, combiner, env = a:match({inferred_expression(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)
    if not ok then return false, combiner end
    args = b
  end

  
  -- resolve first of the pair as an expression
  -- typecheck it
  -- check type to see how it should be combined
  -- either
  --   resolve rest of the pair as collect tuple
  --   pass it into the operative's arguments


  -- combiner was an evaluated typed value, now it isn't
  local type_of_term, usage_count, term = infer(combiner, env.typechecking_context)

  local ok, as_operative = type_of_term:as_operative_type()
  if ok then
    -- FIXME: this doesn't exist yet and API might change
    -- operative input: env, syntax tree, target type
    local operative_result_val = terms.apply_value(as_operative.closure, terms.values.prim_tuple(value_array(env, args))
    -- result should be able to be an inferred term, can fail
    if operative_result_val.kind ~= "value_data" then
      return false, "applying operative did not result in value_data type, typechecker or lua operative mistake when applying at " .. a.anchor .. " to the args at " .. b.anchor
    end
    if operative_result_val.variant == "error" then
      return false, semantic_error.operative_apply_failed(operative_result_val.data, a.anchor, b.anchor)
    end
    -- FIXME: assert type is an inferrable term using new API once it exists
    local resulting_type, usage_counts, term = infer(env, operative_result_val.data)
    return true, inferrable_term.typed(resulting_type, usage_counts, term), env
  end

  if type_of_term:is_qtype() and type_of_term.type:is_pi() then
    -- multiple quantity of usages in tuple with usage in function arguments
    local ok, tuple, env = args:match({inferred_collect_tuple(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)

    if not ok then
      return false, tuple, env
    end

    return inferrable_term.application(inferrable_term.typed(type_of_term, usage_count, term), tuple)
  end

  if type_of_term:is_qtype() and type_of_term.type:as_prim_function_type() then
    -- multiple quantity of usages in tuple with usage in function arguments
    local ok, tuple, env = args:match({inferred_collect_prim_tuple(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)

    if not ok then
      return false, tuple, env
    end

    return true, inferrable_term.application(inferrable_term.typed(type_of_term, usage_count, term), tuple), env
  end

  p(type_of_term)
  return false, "unknown type for pairhandler " .. type_of_term.kind, env
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
    return true,
      inferrable_term.typed(
        unrestricted(value.prim_number_type),
        usage_array(),
        typed_term.literal(value.prim(val.val))
      ), env
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
  -- what we're going for:
  -- (s : syntax, e : environment, u : wrapped_typed_term(userdata), g : goal) -> (goal_to_term(g), environment)
  -- what we have:
  -- (s : syntax, e : environment) -> (inferrable_term, environment)

  -- 1: wrap fn as a typed prim
  -- this way it can take a prim tuple and return a prim tuple
  local typed_prim_fn = typed_term.literal(value.prim(fn))
  -- 2: wrap it to convert a normal tuple argument to a prim tuple
  -- and a prim tuple result to a normal tuple
  -- this way it can take a normal tuple and return a normal tuple
  local nparams = 2 -- for convenience when we upgrade to 4
  local tuple_conv_elements = typed_array()
  local prim_tuple_conv_elements = typed_array()
  for i = 1, nparams do
    -- + 1 because variable 1 is the argument tuple
    -- all variables that follow are the destructured tuple
    local var = typed_term.bound_variable(i + 1)
    tuple_conv_elements:append(var)
    prim_tuple_conv_elements:append(var)
  end
  local tuple_conv = typed_term.tuple_cons(tuple_conv_elements)
  local prim_tuple_conv = typed_term.prim_tuple_cons(prim_tuple_conv_elements)
  local tuple_to_prim_tuple = typed_term.tuple_elim(typed_term.bound_variable(1), nparams, prim_tuple_conv)
  local tuple_to_prim_tuple_fn = typed_term.application(typed_prim_fn, tuple_to_prim_tuple)
  local tuple_to_tuple_fn = typed_term.tuple_elim(tuple_to_prim_tuple_fn, nparams, tuple_conv)
  -- 3: wrap it in a closure with an empty capture, not a typed lambda
  -- this ensures variable 1 is the argument tuple
  local typed_fn = typed_term.literal(value.closure(tuple_to_tuple_fn, runtime_context()))
  -- 4: wrap it in an inferrable term
  -- note how it takes a normal tuple and returns a normal tuple
  local cu_syntax_type = const_combinator(unrestricted(prim_syntax_type))
  local cu_inf_type = const_combinator(unrestricted(prim_inferrable_term_type))
  local cu_env_type = const_combinator(unrestricted(prim_environment_type))
  local param_type = unrestricted(value.tuple_type(cons(cons(empty, cu_syntax_type), cu_env_type)))
  local result_type = unrestricted(value.tuple_type(cons(cons(empty, cu_inf_type), cu_env_type)))
  local inferred_type = value.pi(param_type, param_info_explicit, result_type, result_info_pure)
  local inferrable_fn = inferrable_term.typed(inferred_type, usage_array(), typed_fn)
  -- 5: wrap it in an operative type cons and finally an operative cons
  -- with empty userdata
  local userdata_type = unrestricted(value.tuple_type(empty))
  local userdata_type_term = typed_term.literal(userdata_type)
  local userdata_type_inf = inferrable_term.typed(value.star(0), usage_array(), userdata_type_term)
  local op_type_fn = inferrable_term.operative_type_cons(checkable_term.inferrable(inferrable_fn), userdata_type_inf)
  local userdata = inferrable_term.tuple_cons(inferrable_array())
  local op_fn = inferrable_term.operative_cons(op_type_fn, userdata)
  return op_fn
end

local function inferred_collect_tuple_pair_handler(env, a, b)
  local ok, val, env = a:match({inferred_expression(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)
  if not ok then return false, val end
  return true, true, val, b, env
end

local function inferred_collect_tuple_nil_handler(env) return true, false, nil, nil, env end

inferred_collect_tuple = metalanguage.reducer(function(syntax, _, env)
  local collected_terms = inferrable_array()
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
  return true, inferrable_term.tuple_cons(collected_terms), env
end, "inferred_collect_tuple")

inferred_collect_prim_tuple = metalanguage.reducer(function(syntax, _, env)
    local collected_terms = inferrable_array()
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
    return true, inferrable_term.prim_tuple_cons(collected_terms), env
end, "inferred_collect_prim_stuple")

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
