local terms = require './terms'
local runtime_context = terms.runtime_context
local typechecking_context = terms.typechecking_context
local checkable_term = terms.checkable_term
local mechanism_term = terms.mechanism_term
local mechanism_usage = terms.mechanism_usage
local inferrable_term = terms.inferrable_term
local typed_term = terms.typed_term
local free = terms.free
local quantity = terms.quantity
local visibility = terms.visibility
local purity = terms.purity
local result_info = terms.result_info
local value = terms.value
local neutral_value = terms.neutral_value

local gen = require './terms-generators'
local map = gen.declare_map
local array = gen.declare_array
local value_array = array(value)
local typed_term_array = array(typed_term)
local primitive_value_array = array(gen.any_lua_type)
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
local function prim_tup_val(...) return value.prim_tuple_value(primitive_value_array(...)) end

local derivers = require './derivers'

--[[
local function extract_value_metavariable(value) -- -> Option<metavariable>
  if value.kind == "value_neutral" and value.neutral.kind == "neutral_value_free" and value.neutral.free.kind == "free_metavariable" then
    return value.neutral.free.metavariable
  end
  return nil
end

local is_value = gen.metatable_equality(value)

local function unify(
    first_value,
    params,
    variant,
    second_value)
  -- -> unified value,
  if first_value == second_value then
    return first_value
  end

  local first_mv = extract_value_metavariable(first_value)
  local second_mv = extract_value_metavariable(second_value)

  if first_mv and second_mv then
    first_mv:bind_metavariable(second_mv)
    return first_mv:get_canonical()
  elseif first_mv then
    return first_mv:bind_value(second_value)
  elseif second_mv then
    return second_mv:bind_value(first_value)
  end

  if first_value.kind ~= second_value.kind then
    error("can't unify values of kinds " .. first_value.kind .. " and " .. second_value.kind)
  end

  local unified_args = {}
  local prefer_left = true
  local prefer_right = true
  for i, v in ipairs(params) do
    local first_arg = first_value[v]
    local second_arg = second_value[v]
    if is_value(first_arg) then
      local u = first_arg:unify(second_arg)
      unified_args[i] = u
      prefer_left = prefer_left and u == first_arg
      prefer_right = prefer_right and u == second_arg
    elseif first_arg == second_arg then
      unified_args[i] = first_arg
    else
      p("unify args", first_value, second_value)
      error("unification failure as " .. v .. " field value doesn't match")
    end
  end

  if prefer_left then
    return first_value
  elseif prefer_right then
    return second_value
  else
    -- create new value
    local first_type = getmetatable(first_value)
    local cons = first_type
    if variant then
      cons = first_type[variant]
    end
    local unified = cons(table.unpack(unified_args))
    return unified
  end
end

local unifier = {
  record = function(t, info)
    t.__index = t.__index or {}
    function t.__index:unify(second_value)
      return unify(self, info.params, nil, second_value)
    end
  end,
  enum = function(t, info)
    t.__index = t.__index or {}
    function t.__index:unify(second_value)
      local vname = string.sub(self.kind, #info.name + 2, -1)
      return unify(self, info.variants[vname].info.params, vname, second_value)
    end
  end,
}

value:derive(unifier)
result_info:derive(unifier)
]]

value:derive(derivers.eq)

local evaluate, infer

local function check(
    checkable_term, -- constructed from checkable_term
    typechecking_context, -- todo
    target_type) -- must be unify with target type (there is some way we can assign metavariables to make them equal)
  -- -> type of that term, a typed term

  if checkable_term.kind == "inferred" then
    local inferred_type, typed_term = infer(checkable_term.inferred_term, typechecking_context)
    unified_type = inferred_type:unify(target_type) -- can fail, will cause lua error
    return unified_type, typed_term
  elseif checkable_term.kind == "checked_lambda" then
    -- assert that target_type is a pi type
    -- TODO open says work on other things first they will be easier
  end

  error("check: unknown kind: " .. checkable_term.kind)
end

local function add_arrays(onto, with)
  local olen = #onto
  for i, n in ipairs(with) do
    local x
    if i > olen then
      x = 0
    else
      x = onto[i]
    end
    onto[i] = x + n
  end
end

local function substitute_type_variables(val, index_base, index_offset)
  -- TODO: replace free_placeholder variables with bound variables
  return value.closure(typed_term.literal(val), runtime_context())
end

local function infer_mechanism(mechanism_term, typechecking_context, mechanism_usage)
  local ok, inferrable_term = mechanism_term:as_inferrable()
  if ok then
    return infer(inferrable_term, typechecking_context)
  end

  local ok, param_name, body = mechanism_term:as_lambda()
  if ok then
    local ok, arg_type, next_usage = mechanism_usage:as_callable()
    if not ok then
      error("infer_mechanism: can't infer mechanism type because mechanism lambda wasn't called immediately")
    end
    local inner_context = typechecking_context:append(param_name, arg_type)
    local inner_type, inner_usages, inner_term = infer_mechanism(body, inner_context, next_usage)
    local res_type = value.pi(arg_type, param_info_explicit, inner_type, result_info_pure)
    -- TODO: handle quantities
    return linear(res_type), inner_usages:copy(1, #inner_usages - 1), typed_term.lambda(inner_term)
  end
end

local function apply_value(f, arg)
  local ok, code, capture = f:as_closure()
  if ok then
    return evaluate(code, capture:append(arg))
  end

  local ok, neutral = f:as_neutral()
  if ok then
    return value.neutral(neutral_value.application_stuck(neutral, arg))
  end

  local ok, primitive_value = f:as_prim()
  if ok then
    local ok, elements = arg:as_prim_tuple_value()
    if ok then
      return prim_tup_val(primitive_value(elements:unpack()))
    end

    local ok, neutral = arg:as_neutral()
    if ok then
      return value.neutral(neutral_value.prim_application_stuck(primitive_value, neutral))
    end

    error("apply_value: trying to apply a primitive function on a non-primitive value")
  end

  p(f)
  error("apply_value: trying to apply function application to something that isn't a function/closure")
end

local function eq_prim_tuple_value_decls(left, right, typechecking_context)
  if left.constructor == "empty" and right.constructor == "empty" then
    return typechecking_context
  elseif left.constructor == "empty" or right.constructor == "empty" then
    error("eq_prim_tuple_value_decls: mismatch in number of expected and given args in primitive function application")
  elseif left.constructor == "cons" and right.constructor == "cons" then
    local left_details = left.arg.elements
    local right_details = right.arg.elements
    local context = eq_prim_tuple_value_decls(left_details[1], right_details[1], typechecking_context)
    local left_f = left_details[2]
    local right_f = right_details[2]
    local elements = value_array()
    local runtime_context = context:get_runtime_context()
    for i = #typechecking_context + 1, #context do
      elements:append(runtime_context:get(i))
    end
    local arg = value.tuple_value(elements)
    local left_type = apply_value(left_f, arg)
    local right_type = apply_value(right_f, arg)
    if left_type == right_type then
      local new_context = context:append("", left_type)
      return new_context
    else
      print("mismatch")
      p(left_type)
      p(right_type)
      error("eq_prim_tuple_value_decls: type mismatch in primitive function application")
    end
  else
    error("eq_prim_tuple_value_decls: unknown tuple type data constructor")
  end
end

function infer(
    inferrable_term, -- constructed from inferrable
    typechecking_context -- todo
    )
  -- -> type of term, usage counts, a typed term,
  -- TODO: typecheck inferrable_term and typechecking_context?

  local ok, index = inferrable_term:as_bound_variable()
  if ok then
    local typeof_bound = typechecking_context:get_type(index)
    local usage_counts = usage_array()
    local context_size = #typechecking_context
    for i = 1, context_size do usage_counts:append(0) end
    usage_counts[index] = 1
    local bound = typed_term.bound_variable(index)
    return typeof_bound, usage_counts, bound
  end

  local ok, t, usage_counts, t_term = inferrable_term:as_typed()
  if ok then
    return t, usage_counts, t_term
  end

  local ok, param_name, param_annotation, body = inferrable_term:as_annotated_lambda()
  if ok then
    local _, _, param_term = infer(param_annotation, typechecking_context)
    local param_value = evaluate(param_term, typechecking_context:get_runtime_context())
    -- TODO: also handle neutral values, for inference of qtype
    local param_quantity, param_t = param_value:unwrap_qtype()
    local param_quantity = param_quantity:unwrap_quantity()
    local inner_context = typechecking_context:append(param_name, param_t)
    local body_type, body_usages, body_term = infer(body, inner_context)
    local result_type = substitute_type_variables(body_type, #inner_context, 0)
    local body_usages_param = body_usages[#body_usages]
    local lambda_usages = body_usages:copy(1, #body_usages - 1)
    if param_quantity:is_erased() then
      if body_usages_param > 0 then
        error("infer: trying to use an erased parameter")
      end
    elseif param_quantity:is_linear() then
      if body_usages_param > 1 then
        error("infer: trying to use a linear parameter multiple times")
      end
    elseif param_quantity:is_unrestricted() then
      -- nwn
    else
      error("infer: unknown quantity")
    end
    local lambda_type = value.pi(
      param_value,
      param_info_explicit,
      result_type,
      result_info_pure
    )
    local lambda_term = typed_term.lambda(body_term)
    -- TODO: handle quantities
    return unrestricted(lambda_type), lambda_usages, lambda_term
  end

  local ok, quantity, t = inferrable_term:as_qtype()
  if ok then
    local quantity_type, quantity_usages, quantity_term = infer(quantity, typechecking_context)
    local type_type, type_usages, type_term = infer(t, typechecking_context)
    local qtype_usages = usage_array()
    add_arrays(qtype_usages, quantity_usages)
    add_arrays(qtype_usages, type_usages)
    local qtype = typed_term.qtype(quantity_term, type_term)
    local qtype_type = value.qtype_type(0) -- TODO: get level from the inner type
    return qtype_type, qtype_usages, qtype
  end

  local ok, param_type, param_info, result_type, result_info = inferrable_term:as_pi()
  if ok then
    error("infer: nyi")
    local param_type_type, param_type_usages, param_type_term = infer(param_type, typechecking_context)
    local param_info_type, param_info_usages, param_type_term = infer(param_type, typechecking_context)
    local param_type_type, param_type_usages, param_type_term = infer(param_type, typechecking_context)
    local param_type_type, param_type_usages, param_type_term = infer(param_type, typechecking_context)
  end

  local ok, f, arg = inferrable_term:as_application()
  if ok then
    local f_type, f_usages, f_term = infer(f, typechecking_context)
    local f_quantity, f_t = f_type:unwrap_qtype()
    local arg_type, arg_usages, arg_term = infer(arg, typechecking_context)
    local arg_quantity, arg_t = arg_type:unwrap_qtype()
    local application_usages = usage_array()
    add_arrays(application_usages, f_usages)
    add_arrays(application_usages, arg_usages)
    local application = typed_term.application(f_term, arg_term)

    local ok, f_param_type, f_param_info, f_result_type, f_result_info = f_t:as_pi()
    if ok then
      if not f_param_info:unwrap_param_info():unwrap_visibility():is_explicit() then
        error("infer: nyi implicit parameters")
      end
      if f_param_type ~= arg_type then
        p(f_param_type)
        p(arg_type)
        error("infer: mismatch in arg type and param type of function application")
      end
      local application_result_type = apply_value(f_result_type, evaluate(arg_term, typechecking_context:get_runtime_context()))
      return application_result_type, application_usages, application
    end

    local ok, f_param_type, f_result_type = f_t:as_prim_function_type()
    if ok then
      local f_param_quantity, f_param_t = f_param_type:unwrap_qtype()
      local f_decls = f_param_t:unwrap_prim_tuple_type()
      local arg_decls = arg_t:unwrap_prim_tuple_type()
      -- will error if not equal/unifiable
      eq_prim_tuple_value_decls(f_decls, arg_decls, typechecking_context)
      return f_result_type, application_usages, application
    end

    p(f_t)
    error("infer: trying to apply function application to something whose type isn't a function type")
  end

  local ok, elements = inferrable_term:as_tuple_cons()
  if ok then
    -- type_data is either "empty", an empty tuple,
    -- or "cons", a tuple with the previous type_data and a function that
    -- takes all previous values and produces the type of the next element
    local type_data = value.data_value("empty", tup_val())
    local usages = usage_array()
    local new_elements = typed_term_array()
    for _, v in ipairs(elements) do
      local e_type, e_usages, e_term = infer(v, typechecking_context)

      local new_type_elements = value_array(type_data, substitute_type_variables(e_type, #typechecking_context + 1, 0))
      type_data = value.data_value("cons", value.tuple_value(new_type_elements))

      add_arrays(usages, e_usages)
      new_elements:append(e_term)
    end
    -- TODO: handle quantities
    return unrestricted(value.tuple_type(type_data)), usages, typed_term.tuple_cons(new_elements)
  end

  local ok, elements = inferrable_term:as_prim_tuple_cons()
  if ok then
    -- type_data is either "empty", an empty tuple,
    -- or "cons", a tuple with the previous type_data and a function that
    -- takes all previous values and produces the type of the next element
    -- TODO: it is a type error to put something that isn't a prim into a prim tuple
    local type_data = value.data_value("empty", tup_val())
    local usages = usage_array()
    local new_elements = typed_term_array()
    for _, v in ipairs(elements) do
      local e_type, e_usages, e_term = infer(v, typechecking_context)

      local new_type_elements = value_array(type_data, substitute_type_variables(e_type, #typechecking_context + 1, 0))
      type_data = value.data_value("cons", value.tuple_value(new_type_elements))

      add_arrays(usages, e_usages)
      new_elements:append(e_term)
    end
    -- TODO: handle quantities
    return unrestricted(value.prim_tuple_type(type_data)), usages, typed_term.prim_tuple_cons(new_elements)
  end

  local ok, mechanism, subject = inferrable_term:as_tuple_elim()
  if ok then
    local subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
    local subject_quantity, subject_t = subject_type:unwrap_qtype()
    -- evaluating the subject is necessary for inferring the type of the mechanism
    local subject_value = evaluate(subject_term, typechecking_context:get_runtime_context())
    local decls, make_prefix

    local ok, subject_decls = subject_t:as_tuple_type()
    if ok then
      decls = subject_decls
      local pass = false
      local ok, subject_elements = subject_value:as_tuple_value()
      if ok then
        pass = true
        local n = #subject_elements
        function make_prefix(i)
          return value.tuple_value(subject_elements:copy(1, n - i))
        end
      end

      local ok, neutral = subject_value:as_neutral()
      if ok then
        pass = true
        error("nyi")
        function make_prefix(i)
        end
      end

      if not pass then
        error("infer: trying to apply tuple elimination to something that isn't a tuple")
      end
    end

    local ok, subject_decls = subject_t:as_prim_tuple_type()
    if ok then
      decls = subject_decls
      local pass = false
      local ok, subject_elements = subject_value:as_prim_tuple_value()
      if ok then
        pass = true
        local n = #subject_elements
        function make_prefix(i)
          return value.prim_tuple_value(subject_elements:copy(1, n - i))
        end
      end

      local ok, neutral = subject_value:as_neutral()
      if ok then
        pass = true
        error("nyi")
        function make_prefix(i)
        end
      end

      if not pass then
        error("infer: trying to apply primitive tuple elimination to something that isn't a primitive tuple")
      end
    end

    if not decls then
      error("infer: trying to apply tuple elimination to something whose type isn't a tuple type")
    end

    local n_elements = 0
    local mech_usage = mechanism_usage.inferrable
    while true do
      local constructor, arg = decls:unwrap_data_value()
      if constructor == "empty" then
        break
      elseif constructor == "cons" then
        n_elements = n_elements + 1
        local prefix = make_prefix(n_elements)
        local details = arg:unwrap_tuple_value()
        local f = details[2]
        local element_type = apply_value(f, prefix)
        mech_usage = mechanism_usage.callable(element_type, mech_usage)
        decls = details[1]
      else
        error("infer: unknown tuple type data constructor")
      end
    end

    local mech_type, mech_usages, mech_term = infer_mechanism(mechanism, typechecking_context, mech_usage)
    local result_type = mech_type
    for i = 1, n_elements do
      local result_quantity, result_t = result_type:unwrap_qtype()
      local result_param_type, result_param_info, result_result_type, result_result_info = result_t:unwrap_pi()
      result_type = result_result_type
    end
    local result_usages = usage_array()
    add_arrays(result_usages, subject_usages)
    add_arrays(result_usages, mech_usages)
    return result_type, result_usages, typed_term.tuple_elim(mech_term, subject_term)
  end

  local ok, handler = inferrable_term:as_operative_cons()
  if ok then
    error("NYI inferrable_operative_cons")
    local goal_type = value.pi(
      unrestricted(tup_val(unrestricted(value.syntax_type), unrestricted(value.environment_type))),
      param_info_explicit,
      unrestricted(tup_val(unrestricted(value.inferrable_term_type), unrestricted(value.environment_type))),
      result_info_pure
    )
    local unified_type, typed_operative = check(handler, typechecking_context, goal_type)
  end

  local ok, id, family_args = inferrable_term:as_prim_user_defined_type_cons()
  if ok then
    local new_family_args = typed_term_array()
    local result_usages = usage_array()
    for _, v in ipairs(family_args) do
      local e_type, e_usages, e_term = infer(v, runtime_context)
      -- FIXME: use e_type?
      add_arrays(result_usages, e_usages)
      new_family_args:append(e_term)
    end
    return value.prim_type_type, result_usages, typed_term.prim_user_defined_type_cons(id, new_family_args)
  end

  --[[
  if inferrable_term.kind == "inferrable_level0" then
    return value.level_type, typed_term.level0
  elseif inferrable_term.kind == "inferrable_level_suc" then
    local arg_type, arg_term = infer(inferrable_term.previous_level, typechecking_context)
    arg_type:unify(value.level_type)
    return value.level_type, typed_term.level_suc(arg_term)
  elseif inferrable_term.kind == "inferrable_level_max" then
    local arg_type_a, arg_term_a = infer(inferrable_term.level_a, typechecking_context)
    local arg_type_b, arg_term_b = infer(inferrable_term.level_b, typechecking_context)
    arg_type_a:unify(value.level_type)
    arg_type_b:unify(value.level_type)
    return value.level_type, typed_term.level_max(arg_term_a, arg_term_b)
  elseif inferrable_term.kind == "inferrable_level_type" then
    return value.star(0), typed_term.level_type
  elseif inferrable_term.kind == "inferrable_star" then
    return value.star(1), typed_term.star(0)
  elseif inferrable_term.kind == "inferrable_prop" then
    return value.star(1), typed_term.prop(0)
  elseif inferrable_term.kind == "inferrable_prim" then
    return value.star(1), typed_term.prim
  end
  ]]

  error("infer: unknown kind: " .. inferrable_term.kind)
end

function evaluate(
    typed_term,
    runtime_context
    )
  -- -> a value
  -- TODO: typecheck typed_term and runtime_context?

  local ok, index = typed_term:as_bound_variable()
  if ok then
    return runtime_context:get(index)
  end

  local ok, literal_value = typed_term:as_literal()
  if ok then
    return literal_value
  end

  local ok, body = typed_term:as_lambda()
  if ok then
    return value.closure(body, runtime_context)
  end

  local ok, quantity, t = typed_term:as_qtype()
  if ok then
    local quantity_value = evaluate(quantity, runtime_context)
    local type_value = evaluate(t, runtime_context)
    return value.qtype(quantity_value, type_value)
  end

  local ok, param_type, param_info, result_type, result_info = typed_term:as_pi()
  if ok then
    local param_type_value = evaluate(param_type, runtime_context)
    local param_info_value = evaluate(param_info, runtime_context)
    local result_type_value = evaluate(result_type, runtime_context)
    local result_info_value = evaluate(result_info, runtime_context)
    return value.pi(param_type_value, param_info_value, result_type_value, result_info_value)
  end

  local ok, f, arg = typed_term:as_application()
  if ok then
    local f_value = evaluate(f, runtime_context)
    local arg_value = evaluate(arg, runtime_context)
    return apply_value(f_value, arg_value)
  end

  local ok, elements = typed_term:as_tuple_cons()
  if ok then
    local new_elements = value_array()
    for _, v in ipairs(elements) do
      new_elements:append(evaluate(v, runtime_context))
    end
    return value.tuple_value(new_elements)
  end

  local ok, mechanism, subject = typed_term:as_tuple_elim()
  if ok then
    local mechanism_value = evaluate(mechanism, runtime_context)
    local subject_value = evaluate(subject, runtime_context)

    local ok, subject_elements = subject_value:as_tuple_value()
    if ok then
      local mechacons = mechanism_value
      for _, v in ipairs(subject_elements) do
        mechacons = apply_value(mechacons, v)
      end
      return mechacons
    end

    local ok, subject_elements = subject_value:as_prim_tuple_value()
    if ok then
      local mechacons = mechanism_value
      for _, v in ipairs(subject_elements) do
        mechacons = apply_value(mechacons, value.prim(v))
      end
      return mechacons
    end

    local ok, subject_neutral = subject_value:as_neutral()
    if ok then
      return value.neutral(neutral_value.tuple_elim_stuck(mechanism_value, subject_neutral))
    end

    error("evaluate: trying to apply tuple elimination to something that isn't a tuple")
  end

  if typed_term:is_operative_cons() then
    return value.operative_value
  end

  local ok, elements = typed_term:as_prim_tuple_cons()
  if ok then
    local new_elements = primitive_value_array()
    local stuck = false
    local stuck_element
    local trailing_values
    for _, v in ipairs(elements) do
      local element_value = evaluate(v, runtime_context)
      if stuck then
        trailing_values:append(element_value)
      else
        local ok, primitive_value = element_value:as_prim()
        if ok then
          new_elements:append(primitive_value)
          goto continue_eval_prim_tuple_cons
        end
        local ok, neutral = element_value:as_neutral()
        if ok then
          stuck = true
          stuck_element = neutral
          trailing_values = value_array()
          goto continue_eval_prim_tuple_cons
        end
        error("evaluate: trying to apply primitive tuple construction with something that isn't a primitive value")
      end
      ::continue_eval_prim_tuple_cons::
    end
    if stuck then
      return value.neutral(neutral_value.prim_tuple_stuck(new_elements, stuck_element, trailing_values))
    else
      return value.prim_tuple_value(new_elements)
    end
  end

  local ok, id, family_args = typed_term:as_prim_user_defined_type_cons()
  if ok then
    local new_family_args = value_array()
    for _, v in ipairs(family_args) do
      new_family_args:append(evaluate(v, runtime_context))
    end
    return value.prim_user_defined_type(id, new_family_args)
  end

  --[[
  if typed_term.kind == "typed_level0" then
    return value.level(0)
  elseif typed_term.kind == "typed_level_suc" then
    local previous_level = evaluate(typed_term.previous_level, runtime_context)
    if previous_level.kind ~= "value_level" then
      p(previous_level)
      error("wrong type for previous_level")
    end
    if previous_level.level > 10 then
      error("NYI: level too high for typed_level_suc" .. tostring(previous_level.level))
    end
    return value.level(previous_level.level + 1)
  elseif typed_term.kind == "typed_level_max" then
    local level_a = evaluate(typed_term.level_a, runtime_context)
    local level_b = evaluate(typed_term.level_b, runtime_context)
    if level_a.kind ~= "value_level" or level_b.kind ~= "value_level" then
      error("wrong type for level_a or level_b")
    end
    return value.level(math.max(level_a.level, level_b.level))
  elseif typed_term.kind == "typed_level_type" then
    return value.level_type
  elseif typed_term.kind == "typed_star" then
    return value.star(typed_term.level)
  elseif typed_term.kind == "typed_prop" then
    return value.prop(typed_term.level)
  elseif typed_term.kind == "typed_prim" then
    return value.prim
  end
  ]]

  error("evaluate: unknown kind: " .. typed_term.kind)
end

return {
  check = check,
  infer = infer,
  evaluate = evaluate,
}
