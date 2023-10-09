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
local name_array = array(gen.builtin_string)

local function qtype(q, val) return value.qtype(value.quantity(q), val) end
local function unrestricted(val) return qtype(quantity.unrestricted, val) end
local function default_unrestricted(val)
  if val:is_qtype() then
    return val
  end
  return qtype(quantity.unrestricted, val)
end
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
  end,
  operative_apply_failed = function(result, anchors)
    return {
      text = "operative apply failed",
      result = result,
      anchors = anchors,
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
  -- local ok, ifx, op, args = b:match(
  --   {
  --     metalanguage.is_pair(check_infix_expression_handler)
  --   },
  --   metalanguage.failure_handler,
  --   {env = env, prec = 0, lhs = a}
  -- )

  local ok, ifx = true, false

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

  local ok, handler, userdata_type = type_of_term:as_operative_type()
  if ok then
    -- operative input: env, syntax tree, target type (if checked)
		local tuple_args = array(gen.any_lua_type)(args, env)
    local operative_result_val = evaluator.apply_value(handler, terms.value.prim_tuple_value(tuple_args))
    -- result should be able to be an inferred term, can fail
		-- NYI: operative_cons in evaluator must use Maybe type once it exists
    -- if not operative_result_val:is_data_value() then
		-- 	p(operative_result_val.kind)
		-- 	print(operative_result_val:pretty_print())
		-- 	return false, "applying operative did not result in value term with kind data_value, typechecker or lua operative mistake when applying " .. tostring(a.anchor) .. " to the args " .. tostring(b.anchor)
    -- end
		-- variants: ok, error
    if operative_result_val.variant == "error" then
      return false, semantic_error.operative_apply_failed(operative_result_val.data, {a.anchor, b.anchor})
    end

		-- temporary, while it isn't a Maybe
		local data = operative_result_val.elements[1].primitive_value
		local env = operative_result_val.elements[2].primitive_value

    -- FIXME: assert type is an inferrable term using new API once it exists
		if not inferrable_term.value_check(data) then error "tried to handle something that was not an inferrable term" end
		p("Inferring!", data.kind, env.typechecking_context)

    local resulting_type, usage_counts, term = infer(data, env.typechecking_context)

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

local function split_dot_accessors(str)
	return str:match("([^.]+)%.(.+)")
end

local function inferred_expression_symbolhandler(env, name)
  --print("looking up symbol", name)
  --p(env)
	print(name, split_dot_accessors(name))
	local front, rest = split_dot_accessors(name)
	if not front then
		local ok, val = env:get(name)
		return ok, val, env
	else
		local ok, part = env:get(front)
		if not ok then return ok, part end
		while front do
			name = rest
			front, rest = split_dot_accessors(name)
			part = inferrable_term.record_elim(
				part,
				name_array(front or name),
				inferrable_term.bound_variable(#env.typechecking_context + 1)
			)
		end
		return ok, part, env
	end
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
	if val.type == "string" then
    return true,
      inferrable_term.typed(
        unrestricted(value.prim_string_type),
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
    function(syntax, environment)
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
    function(syntax, environment)
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
	local aborting_fn = function(syn, env)
		local ok, res, env = fn(syn, env)
		if not ok then
			error("Primitive operative apply failure, NYI convert to Maybe.\nError was:" .. tostring(res))
		end
		return res, env
	end
  -- what we're going for:
  -- (s : syntax, e : environment, u : wrapped_typed_term(userdata), g : goal) -> (goal_to_term(g), environment)
	--   goal one of inferable, mechanism, checkable
  -- what we have:
  -- (s : syntax, e : environment) -> (inferrable_term, environment)

  -- 1: wrap fn as a typed prim
  -- this way it can take a prim tuple and return a prim tuple
  local typed_prim_fn = typed_term.literal(value.prim(aborting_fn))
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
	local error_type = terms.prim_lua_error_type
  local param_type = unrestricted(value.tuple_type(cons(cons(empty, cu_syntax_type), cu_env_type)))

	-- tuple_of(ok) -> prim_if(ok, prim_inferrable_term_type, error_type)
	-- FIXME: once operative_cons makes the correct type with a Maybe, put this back and convert to Maybe
	-- For now, we handle with a lua abort inside the primitive operative
	-- local inf_term_or_error = value.closure(
	-- 	typed_term.prim_if(
	-- 		typed_term.tuple_elim(typed_term.bound_variable(3), 1, typed_term.bound_variable(4)), -- how do I get the first thing in the input tuple?
	-- 		typed_term.bound_variable(1),
	-- 		typed_term.bound_variable(2)
	-- 	),
	-- 	runtime_context():append(unrestricted(prim_inferrable_term_type)):append(error_type)
	-- )
	-- local result_type = const_combinator(unrestricted(value.tuple_type(
	-- 	cons(
	-- 		cons(
	-- 			cons(empty, const_combinator(unrestricted(terms.value.prim_bool_type))),
	-- 			inf_term_or_error
	-- 		),
	-- 		const_combinator(unrestricted(prim_environment_type))
	-- 	)
	-- )))
  local result_type = const_combinator(unrestricted(value.tuple_type(cons(cons(empty, cu_inf_type), cu_env_type))))
  local inferred_type = value.pi(param_type, param_info_explicit, result_type, result_info_pure)
  local inferrable_fn = inferrable_term.typed(inferred_type, usage_array(), typed_fn)
	-- FIXME: use prim_if here
  -- 5: wrap it in an operative type cons and finally an operative cons
  -- with empty userdata
  local userdata_type = unrestricted(value.tuple_type(empty))
  local userdata_type_term = typed_term.literal(userdata_type)
  local userdata_type_inf = inferrable_term.typed(value.star(0), usage_array(), userdata_type_term)
  local op_type_fn = inferrable_term.operative_type_cons(terms.checkable_term.inferrable(inferrable_fn), userdata_type_inf)
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

inferred_collect_tuple = metalanguage.reducer(function(syntax, env)
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

inferred_collect_prim_tuple = metalanguage.reducer(function(syntax, env)
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

local expressions_args = metalanguage.reducer(function(syntax, env)
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

local block = metalanguage.reducer(function(syntax, env)
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

-- example usage of primitive_applicative
-- add(a, b) = a + b ->
-- local prim_num = terms.value.prim_number_type
-- primitive_applicative(function(a, b) return a + b end, {prim_num, prim_num}, {prim_num}),

local function build_prim_type_tuple(elems)
  local result = empty
  local quantity = terms.value.quantity(terms.quantity.unrestricted)

  if elems.is_qtype and elems:is_qtype() then
    quantity, elems = elems:unwrap_qtype()
  end

  for i, v in ipairs(elems) do
    result = cons(result, const_combinator(default_unrestricted(v)))
  end

  return terms.value.qtype(quantity, terms.value.prim_tuple_type(result))
end

local function primitive_applicative(fn, params, results)
  local literal_prim_fn = terms.typed_term.literal(terms.value.prim(fn))
  local prim_fn_type = terms.value.prim_function_type(build_prim_type_tuple(params), build_prim_type_tuple(results))

  return terms.inferrable_term.typed(unrestricted(prim_fn_type), usage_array(), literal_prim_fn)
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
