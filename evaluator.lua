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

local function qtype(q, val) return value.qtype(value.quantity(q), val) end
local function unrestricted(val) return qtype(quantity.unrestricted, val) end
local function linear(val) return qtype(quantity.linear, val) end
local function erased(val) return qtype(quantity.erased, val) end
local param_info_explicit = value.param_info(value.visibility(visibility.explicit))
local param_info_implicit = value.param_info(value.visibility(visibility.implicit))
local result_info_pure = value.result_info(result_info(purity.pure))
local result_info_effectful = value.result_info(result_info(purity.effectful))
local function tupval(...) return value.tuple_value(array(value)(...)) end

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
  for i, n in ipairs(with) do
    local x
    if i > #onto then
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
  --print("infer_mechanism")
  --p(mechanism_term)
  --p(typechecking_context)
  --p(mechanism_usage)
  if mechanism_term.kind == "mechanism_inferrable" then
    local mech_type, mech_usages, mech_term = infer(mechanism_term.inferrable_term, typechecking_context)
    --print("printing mech_type!!!!!!!!!!!")
    --p(mech_type)
    return mech_type, mech_usages, mech_term
  elseif mechanism_term.kind == "mechanism_lambda" then
    if mechanism_usage.kind ~= "mechanism_usage_callable" then
      error("infer_mechanism: can't infer mechanism type because mechanism lambda wasn't called immediately")
    end
    local inner_context = typechecking_context:append(mechanism_term.param_name, mechanism_usage.arg_type)
    local inner_type, inner_usages, inner_term = infer_mechanism(mechanism_term.body, inner_context, mechanism_usage.next_usage)
    local res_type = value.pi(
      mechanism_usage.arg_type,
      param_info_explicit,
      inner_type,
      result_info_pure
    )
    -- TODO: handle quantity
    return linear(res_type), inner_usages:copy(1, #inner_usages - 1), typed_term.lambda(inner_term)
  end
end

local function apply_value(f, arg)
  --print("apply_value")
  --p(f)
  --p(arg)
  local kind = f.kind
  if kind == "value_closure" then
    local inner_context = f.capture:append(arg)
    return evaluate(f.code, inner_context)
  elseif kind == "value_neutral" then
    return value.neutral(neutral_value.application_stuck(f.neutral_value, arg))
  elseif kind == "value_prim" then
    if arg.kind == "value_prim_tuple_value" then
      return value.prim_tuple_value(array(gen.any_lua_type)(f.primitive_value(arg.elements:unpack())))
    elseif arg.kind == "value_neutral" then
      return value.neutral(neutral_value.prim_application_stuck(f.primitive_value, arg.neutral_value))
    else
      error("apply_value: trying to apply a primitive function on a non-primitive value")
    end
  else
    p(f)
    error("apply_value: trying to apply function application to something that isn't a function/closure")
  end
end

function infer(
    inferrable_term, -- constructed from inferrable
    typechecking_context -- todo
    )
  -- -> type of term, usage counts, a typed term,

  --print("inferring!")
  --p(inferrable_term)
  --print(inferrable_term.kind)
  -- TODO: typecheck inferrable_term and typechecking_context?
  local usage_array = array(gen.builtin_number)
  local value_array = array(value)
  local primitive_value_array = array(gen.any_lua_type)
  if inferrable_term.kind == "inferrable_bound_variable" then
    local index = inferrable_term.index
    local typeof_bound = typechecking_context:get_type(index)
    local usage_counts = usage_array()
    local context_size = #typechecking_context
    for i = 1, context_size do usage_counts:append(0) end
    usage_counts[index] = 1
    local bound = typed_term.bound_variable(index)
    return typeof_bound, usage_counts, bound
  elseif inferrable_term.kind == "inferrable_typed" then
    return inferrable_term.type, inferrable_term.usage_counts, inferrable_term.typed_term
  elseif inferrable_term.kind == "inferrable_annotated_lambda" then
    local _, _, param_term = infer(inferrable_term.param_annotation, typechecking_context)
    --print("infer, handing off to evaluate")
    --p(param_term)
    --print("let's go")
    local param_value = evaluate(param_term, typechecking_context:get_runtime_context())
    -- TODO: also handle neutral values, for inference of qtype
    if param_value.kind ~= "value_qtype" then
      p(param_value)
      error("infer: lambda annotation without quantity information")
    end
    local param_quantity = param_value.quantity.quantity.kind
    local inner_context = typechecking_context:append(inferrable_term.param_name, param_value.type)
    local body_type, body_usages, body_term = infer(inferrable_term.body, inner_context)
    local result_type = substitute_type_variables(body_type, #inner_context, 0)
    --p("A!")
    --p(body_usages)
    local body_usages_param = body_usages[#body_usages]
    local lambda_usages = body_usages:copy(1, #body_usages - 1)
    --p(body_usages)
    --p("B!")
    if param_quantity == "quantity_erased" then
      if body_usages_param > 0 then
        error("infer: trying to use an erased parameter")
      end
    elseif param_quantity == "quantity_linear" then
      if body_usages_param > 1 then
        error("infer: trying to use a linear parameter multiple times")
      end
    elseif param_quantity == "quantity_unrestricted" then
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
    return lambda_type, lambda_usages, lambda_term
  elseif inferrable_term.kind == "inferrable_qtype" then
    local quantity_type, quantity_usages, quantity_term = infer(inferrable_term.quantity, typechecking_context)
    local type_type, type_usages, type_term = infer(inferrable_term.type, typechecking_context)
    local qtype_usages = usage_array()
    add_arrays(qtype_usages, quantity_usages)
    add_arrays(qtype_usages, type_usages)
    local qtype = typed_term.qtype(quantity_term, type_term)
    local qtype_type = value.qtype_type(0) -- TODO: get level from the inner type
    return qtype_type, qtype_usages, qtype
  elseif inferrable_term.kind == "inferrable_pi" then
    error("infer: nyi")
    local param_type_type, param_type_usages, param_type_term = infer(inferrable_term.param_type, typechecking_context)
    local param_info_type, param_info_usages, param_type_term = infer(inferrable_term.param_type, typechecking_context)
    local param_type_type, param_type_usages, param_type_term = infer(inferrable_term.param_type, typechecking_context)
    local param_type_type, param_type_usages, param_type_term = infer(inferrable_term.param_type, typechecking_context)
  elseif inferrable_term.kind == "inferrable_application" then
    local f_type, f_usages, f_term = infer(inferrable_term.f, typechecking_context)
    local arg_type, arg_usages, arg_term = infer(inferrable_term.arg, typechecking_context)
    -- NYI: handle primitive_function types
    if f_type.kind ~= "value_pi" then
      error("infer: trying to apply function application to something whose type isn't a function type")
    end
    if f_type.param_info.visibility.visibility.kind ~= "visibility_explicit" then
      error("infer: nyi implicit parameters")
    end
    if f_type.param_type ~= arg_type then
      p(f_type)
      p(arg_type)
      error("infer: mismatch in arg type and param type of application")
    end
    local result_type = typed_term.application(typed_term.literal(f_type.result_type), arg_term)
    --print("infer, handing off to evaluate (2)")
    --p(f_type)
    --p(result_type)
    --print("let's go")
    local result_value = evaluate(result_type, typechecking_context:get_runtime_context())
    local application_usages = usage_array()
    add_arrays(application_usages, f_usages)
    add_arrays(application_usages, arg_usages)
    local application = typed_term.application(f_term, arg_term)
    return result_value, application_usages, application
  elseif inferrable_term.kind == "inferrable_tuple_cons" then
    -- type_data is either "empty", an empty tuple,
    -- or "cons", a tuple with the previous type_data and a function that
    -- takes all previous values and produces the type of the next element
    local type_data = value.data_value("empty", tupval())
    local usages = usage_array()
    local elements = array(typed_term)()
    for _, v in ipairs(inferrable_term.elements) do
      local e_type, e_usages, e_term = infer(v, typechecking_context)

      local new_type_elements = value_array(type_data, substitute_type_variables(e_type, #typechecking_context + 1, 0))
      type_data = value.data_value("cons", value.tuple_value(new_type_elements))

      add_arrays(usages, e_usages)
      elements:append(e_term)
    end
    -- TODO: handle quantities
    return unrestricted(value.tuple_type(type_data)), usages, typed_term.tuple_cons(elements)
  elseif inferrable_term.kind == "inferrable_prim_tuple_cons" then
    -- type_data is either "empty", an empty tuple,
    -- or "cons", a tuple with the previous type_data and a function that
    -- takes all previous values and produces the type of the next element
    local type_data = value.data_value("empty", tupval())
    local usages = usage_array()
    local elements = array(typed_term)()
    for _, v in ipairs(inferrable_term.elements) do
      local e_type, e_usages, e_term = infer(v, typechecking_context)

      local new_type_elements = primitive_value_array(type_data, substitute_type_variables(e_type, #typechecking_context + 1, 0))
      type_data = value.data_value("cons", value.prim_tuple_value(new_type_elements))

      add_arrays(usages, e_usages)
      elements:append(e_term)
    end
    -- TODO: handle quantities
    return unrestricted(value.tuple_type(type_data)), usages, typed_term.tuple_cons(elements)
  elseif inferrable_term.kind == "inferrable_tuple_elim" then
    local subject_type, subject_usages, subject_term = infer(inferrable_term.subject, typechecking_context)
    if subject_type.kind ~= "value_qtype" or (subject_type.type.kind ~= "value_tuple_type" and subject_type.type.kind ~= "value_prim_tuple_type") then
      error("infer: trying to apply tuple elimination to something whose type isn't a tuple type")
    end
    local is_prim = subject_type.type.kind == "value_prim_tuple_type"
    -- evaluating the subject is necessary for inferring the type of the mechanism
    local subject_value = evaluate(subject_term, typechecking_context:get_runtime_context())
    local elements = subject_value.elements
    local data = subject_type.type.decls
    local mech_usage = mechanism_usage.inferrable
    local tcons = (is_prim and typed_term.prim_tuple_cons or typed_term.tuple_cons)
    for i = #elements - 1, 0, -1 do
      local prefix
      if is_prim and subject_value.kind == "value_prim_tuple_value" then
        prefix = value.prim_tuple_value(elements:copy(1, i))
      elseif not is_prim and subject_value.kind == "value_tuple_value" then
        prefix = value.tuple_value(elements:copy(1, i))
      elseif subject_value.kind == "value_neutral" then
        local prefix_elements = array(typed_term)()
        for x = 1, i do
          prefix_elements:append(typed_term.bound_variable(x))
        end
        local elim_tower = tcons(prefix_elements)
        for x = 1, #elements do
          elim_tower = typed_term.lambda(elim_tower)
        end
        prefix = value.neutral_value(neutral_value.tuple_elim_stuck(evaluate(elim_tower, runtime_context()), subject_value))
      else
        error("infer: trying to apply tuple elimination to something that isn't a tuple (prim: " .. tostring(is_prim) .. ")")
      end
      if data.constructor == "empty" then
        error("infer: mismatch in length between tuple type decl and tuple value")
      elseif data.constructor == "cons" then
        local details = data.arg.elements
        local f = details[2]
        local element_type = apply_value(f, prefix)
        mech_usage = mechanism_usage.callable(element_type, mech_usage)
        data = details[1]
      else
        error("infer: unknown tuple type data constructor")
      end
    end
    if data.constructor ~= "empty" then
      error("infer: mismatch in length between tuple type decl and tuple value")
    end
    local mech_type, mech_usages, mech_term = infer_mechanism(inferrable_term.mechanism, typechecking_context, mech_usage)
    local result_type = mech_type
    for i = 1, #elements do
      result_type = result_type.type.result_type
    end
    local result_usages = usage_array()
    add_arrays(result_usages, subject_usages)
    add_arrays(result_usages, mech_usages)
    return result_type, result_usages, typed_term.tuple_elim(mech_term, subject_term)
  elseif inferrable_term.kind == "inferrable_operative_cons" then
    local goal_type = value.pi(
      unrestricted(tupval(unrestricted(value.syntax_type), unrestricted(value.environment_type))),
      param_info_explicit,
      unrestricted(tupval(unrestricted(value.inferrable_term_type), unrestricted(value.environment_type))),
      result_info_pure
    )
    local unified_type, typed_operative = check(inferrable_term.handler, typechecking_context, goal_type)
    error("NYI inferrable_operative_cons")
  elseif inferrable_term.kind == "inferrable_prim_user_defined_type_cons" then
    local id = inferrable_term.id
    local family_args = array(typed_term)()
    local result_usages = usage_array()
    for _, v in ipairs(inferrable_term.family_args) do
      local e_type, e_usages, e_term = infer(v, runtime_context)
      -- FIXME: use e_type?
      add_arrays(result_usages, e_usages)
      family_args:append(e_term)
    end
    return terms.value.prim_type_type, result_usages, terms.typed_term.prim_user_defined_type_cons(id, family_args)
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

  --print("evaluating!")
  --p(typed_term)
  -- TODO: typecheck typed_term and runtime_context?
  local value_array = array(value)
  if typed_term.kind == "typed_bound_variable" then
    return runtime_context:get(typed_term.index)
  elseif typed_term.kind == "typed_literal" then
    return typed_term.literal_value
  elseif typed_term.kind == "typed_lambda" then
    local closure_value = value.closure(typed_term.body, runtime_context)
    return closure_value
  elseif typed_term.kind == "typed_qtype" then
    local quantity_value = evaluate(typed_term.quantity, runtime_context)
    local type_value = evaluate(typed_term.type, runtime_context)
    return value.qtype(quantity_value, type_value)
  elseif typed_term.kind == "typed_pi" then
    local param_type_value = evaluate(typed_term.param_type, runtime_context)
    local param_info_value = evaluate(typed_term.param_info, runtime_context)
    local result_type_value = evaluate(typed_term.result_type, runtime_context)
    local result_info_value = evaluate(typed_term.result_info, runtime_context)
    return value.pi(param_type_value, param_info_value, result_type_value, result_info_value)
  elseif typed_term.kind == "typed_application" then
    local f_value = evaluate(typed_term.f, runtime_context)
    local arg_value = evaluate(typed_term.arg, runtime_context)
    return apply_value(f_value, arg_value)
  elseif typed_term.kind == "typed_tuple_cons" then
    local elements = value_array()
    for _, v in ipairs(typed_term.elements) do
      elements:append(evaluate(v, runtime_context))
    end
    return value.tuple_value(elements)
  elseif typed_term.kind == "typed_tuple_elim" then
    local mechanism_value = evaluate(typed_term.mechanism, runtime_context)
    local subject_value = evaluate(typed_term.subject, runtime_context)
    if subject_value.kind == "value_tuple_value" then
      local mechacons = mechanism_value
      for _, v in ipairs(subject_value.elements) do
        mechacons = apply_value(mechacons, v)
      end
      return mechacons
    elseif subject_value.kind == "value_prim_tuple_value" then
      local mechacons = mechanism_value
      for _, v in ipairs(subject_value.elements) do
        mechacons = apply_value(mechacons, value.prim(v))
      end
      return mechacons
    elseif subject_value.kind == "value_neutral" then
      return value.neutral(neutral_value.tuple_elim_stuck(mechanism_value, subject_value.neutral_value))
    else
      error("evaluate: trying to apply tuple elimination to something that isn't a tuple")
    end
  elseif typed_term.kind == "typed_operative_cons" then
    return value.operative_value
  elseif typed_term.kind == "typed_prim_tuple_cons" then
    local elements = array(gen.any_lua_type)()
    local stuck = false
    local stuck_element
    local trailing_values
    for _, v in ipairs(typed_term.elements) do
      local element_value = evaluate(v, runtime_context)
      if stuck == false and element_value.kind == "value_prim" then
        elements:append(element_value.primitive_value)
      elseif stuck == true then
        trailing_values:append(element_value)
      elseif element_value.kind == "value_neutral" then
        stuck = true
        stuck_element = element_value.neutral_value
        trailing_values = value_array()
      else
        error("evaluate: trying to apply primitive tuple construction with something that isn't a primitive value")
      end
    end
    if stuck then
      return value.neutral(neutral_value.prim_tuple_stuck(elements, stuck_element, trailing_values))
    else
      return value.prim_tuple_value(elements)
    end
  elseif typed_term.kind == "typed_prim_user_defined_type_cons" then
    local id = typed_term.id
    local family_args = value_array()
    for _, v in ipairs(typed_term.family_args) do
      family_args:append(evaluate(v, runtime_context))
    end
    return value.prim_user_defined_type(id, family_args)
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
