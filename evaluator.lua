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
  if mechanism_term:is_inferrable() then
    return infer(mechanism_term:unwrap_inferrable(), typechecking_context)
  elseif mechanism_term:is_lambda() then
    local param_name, body = mechanism_term:unwrap_lambda()
    local ok, arg_type, next_usage = mechanism_usage:as_callable()
    if not ok then
      error("infer_mechanism: can't infer mechanism type because mechanism lambda wasn't called immediately")
    end
    local inner_context = typechecking_context:append(param_name, arg_type)
    local inner_type, inner_usages, inner_term = infer_mechanism(body, inner_context, next_usage)
    local res_type = value.pi(arg_type, param_info_explicit, inner_type, result_info_pure)
    -- TODO: handle quantities
    return linear(res_type), inner_usages:copy(1, #inner_usages - 1), typed_term.lambda(inner_term)
  else
    error("infer_mechanism: unknown kind: " .. mechanism_term.kind)
  end
end

local function apply_value(f, arg)
  if f:is_closure() then
    local code, capture = f:unwrap_closure()
    return evaluate(code, capture:append(arg))
  elseif f:is_neutral() then
    return value.neutral(neutral_value.application_stuck(f:unwrap_neutral(), arg))
  elseif f:is_prim() then
    local primitive_value = f:unwrap_prim()
    if arg:is_prim_tuple_value() then
      local elements = arg:unwrap_prim_tuple_value()
      return prim_tup_val(primitive_value(elements:unpack()))
    elseif arg:is_neutral() then
      return value.neutral(neutral_value.prim_application_stuck(primitive_value, arg:unwrap_neutral()))
    else
      error("apply_value: trying to apply a primitive function on a non-primitive value")
    end
  else
    p(f)
    error("apply_value: trying to apply function application to something that isn't a function/closure")
  end
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

  if inferrable_term:is_bound_variable() then
    local index = inferrable_term:unwrap_bound_variable()
    local typeof_bound = typechecking_context:get_type(index)
    local usage_counts = usage_array()
    local context_size = #typechecking_context
    for i = 1, context_size do usage_counts:append(0) end
    usage_counts[index] = 1
    local bound = typed_term.bound_variable(index)
    return typeof_bound, usage_counts, bound
  elseif inferrable_term:is_typed() then
    return inferrable_term:unwrap_typed()
  elseif inferrable_term:is_annotated_lambda() then
    local param_name, param_annotation, body = inferrable_term:unwrap_annotated_lambda()
    local _, _, param_term = infer(param_annotation, typechecking_context)
    local param_value = evaluate(param_term, typechecking_context:get_runtime_context())
    -- TODO: also handle neutral values, for inference of qtype
    local param_quantity, param_type = param_value:unwrap_qtype()
    local param_quantity = param_quantity:unwrap_quantity()
    local inner_context = typechecking_context:append(param_name, param_type)
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
    local lambda_type = value.pi(param_value, param_info_explicit, result_type, result_info_pure)
    local lambda_term = typed_term.lambda(body_term)
    -- TODO: handle quantities
    return unrestricted(lambda_type), lambda_usages, lambda_term
  elseif inferrable_term:is_qtype() then
    local quantity, t = inferrable_term:unwrap_qtype()
    local quantity_type, quantity_usages, quantity_term = infer(quantity, typechecking_context)
    local type_type, type_usages, type_term = infer(t, typechecking_context)
    local qtype_usages = usage_array()
    add_arrays(qtype_usages, quantity_usages)
    add_arrays(qtype_usages, type_usages)
    local qtype = typed_term.qtype(quantity_term, type_term)
    local qtype_type = value.qtype_type(0) -- TODO: get level from the inner type
    return qtype_type, qtype_usages, qtype
  elseif inferrable_term:is_pi() then
    error("infer: nyi")
    local param_type, param_info, result_type, result_info = inferrable_term:unwrap_pi()
    local param_type_type, param_type_usages, param_type_term = infer(param_type, typechecking_context)
    local param_info_type, param_info_usages, param_type_term = infer(param_type, typechecking_context)
    local param_type_type, param_type_usages, param_type_term = infer(param_type, typechecking_context)
    local param_type_type, param_type_usages, param_type_term = infer(param_type, typechecking_context)
  elseif inferrable_term:is_application() then
    local f, arg = inferrable_term:unwrap_application()
    local f_type, f_usages, f_term = infer(f, typechecking_context)
    local f_quantity, f_type = f_type:unwrap_qtype()
    local arg_type, arg_usages, arg_term = infer(arg, typechecking_context)
    local arg_quantity, arg_t = arg_type:unwrap_qtype()
    local application_usages = usage_array()
    add_arrays(application_usages, f_usages)
    add_arrays(application_usages, arg_usages)
    local application = typed_term.application(f_term, arg_term)
    if f_type:is_pi() then
      local f_param_type, f_param_info, f_result_type, f_result_info = f_type:unwrap_pi()
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
    elseif f_type:is_prim_function_type() then
      local f_param_type, f_result_type = f_type:unwrap_prim_function_type()
      local f_param_quantity, f_param_type = f_param_type:unwrap_qtype()
      local f_decls = f_param_type:unwrap_prim_tuple_type()
      local arg_decls = arg_t:unwrap_prim_tuple_type()
      -- will error if not equal/unifiable
      eq_prim_tuple_value_decls(f_decls, arg_decls, typechecking_context)
      return f_result_type, application_usages, application
    else
      p(f_type)
      error("infer: trying to apply function application to something whose type isn't a function type")
    end
  elseif inferrable_term:is_tuple_cons() then
    local elements = inferrable_term:unwrap_tuple_cons()
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
  elseif inferrable_term:is_prim_tuple_cons() then
    local elements = inferrable_term:unwrap_prim_tuple_cons()
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
  elseif inferrable_term:is_tuple_elim() then
    local mechanism, subject = inferrable_term:unwrap_tuple_elim()
    local subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
    local subject_quantity, subject_type = subject_type:unwrap_qtype()

    local decls
    if subject_type:is_tuple_type() then
      decls = subject_type:unwrap_tuple_type()
    elseif subject_type:is_prim_tuple_type() then
      decls = subject_type:unwrap_prim_tuple_type()
    else
      error("infer: trying to apply tuple elimination to something whose type isn't a tuple type")
    end

    -- traverse the first time to find the length of the tuple
    local n_elements = 0
    local decls_cur = decls
    while true do
      local constructor, arg = decls_cur:unwrap_data_value()
      if constructor == "empty" then
        break
      elseif constructor == "cons" then
        n_elements = n_elements + 1
        decls_cur = arg:unwrap_tuple_value()[1]
      else
        error("infer: unknown tuple type data constructor")
      end
    end

    -- evaluating the subject is necessary for inferring the type of the mechanism
    local subject_value = evaluate(subject_term, typechecking_context:get_runtime_context())

    -- define how the parameters for type evaluation should be set up
    local make_prefix
    if subject_value:is_tuple_value() then
      if not subject_type:is_tuple_type() then
        error("infer: mismatch between tuple type and evaluated value")
      end
      local subject_elements = subject_value:unwrap_tuple_value()
      function make_prefix(i)
        return value.tuple_value(subject_elements:copy(1, n_elements - i))
      end
    elseif subject_value:is_prim_tuple_value() then
      if not subject_type:is_prim_tuple_type() then
        error("infer: mismatch between tuple type and evaluated value")
      end
      local subject_elements = subject_value:unwrap_prim_tuple_value()
      function make_prefix(i)
        return value.prim_tuple_value(subject_elements:copy(1, n_elements - i))
      end
    elseif subject_value:is_neutral() then
      local neutral = subject_value:unwrap_neutral()
      function make_prefix(i)
        local prefix_elements = typed_term_array()
        for x = 1, i do
          prefix_elements:append(typed_term.bound_variable(x))
        end
        local elim_tower = typed_term.tuple_cons(prefix_elements)
        for x = 1, n_elements do
          elim_tower = typed_term.lambda(elim_tower)
        end
        return value.neutral(neutral_value.tuple_elim_stuck(evaluate(elim_tower, runtime_context()), subject_value))
      end
    else
      error("infer: mismatch between tuple type and evaluated value")
    end

    -- evaluate the type of the tuple
    local mech_usage = mechanism_usage.inferrable
    local decls_cur = decls
    while true do
      local constructor, arg = decls_cur:unwrap_data_value()
      if constructor == "empty" then
        break
      elseif constructor == "cons" then
        local prefix = make_prefix(n_elements)
        local details = arg:unwrap_tuple_value()
        local f = details[2]
        local element_type = apply_value(f, prefix)
        mech_usage = mechanism_usage.callable(element_type, mech_usage)
        decls_cur = details[1]
      else
        error("infer: unknown tuple type data constructor")
      end
    end

    -- infer the type of the mechanism, now knowing the type of the tuple
    local mech_type, mech_usages, mech_term = infer_mechanism(mechanism, typechecking_context, mech_usage)

    -- unwrap the final result type
    local result_type = mech_type
    for i = 1, n_elements do
      local _, result_t = result_type:unwrap_qtype()
      local _, _, result_result_type, _ = result_t:unwrap_pi()
      result_type = result_result_type
    end
    local result_usages = usage_array()
    add_arrays(result_usages, subject_usages)
    add_arrays(result_usages, mech_usages)
    return result_type, result_usages, typed_term.tuple_elim(mech_term, subject_term)
  elseif inferrable_term:is_operative_cons() then
    local handler = inferrable_term:unwrap_operative_cons()
    error("NYI inferrable_operative_cons")
    local goal_type = value.pi(
      unrestricted(tup_val(unrestricted(value.syntax_type), unrestricted(value.environment_type))),
      param_info_explicit,
      unrestricted(tup_val(unrestricted(value.inferrable_term_type), unrestricted(value.environment_type))),
      result_info_pure
    )
    local unified_type, typed_operative = check(handler, typechecking_context, goal_type)
  elseif inferrable_term:is_prim_user_defined_type_cons() then
    local id, family_args = inferrable_term:unwrap_prim_user_defined_type_cons()
    local new_family_args = typed_term_array()
    local result_usages = usage_array()
    for _, v in ipairs(family_args) do
      local e_type, e_usages, e_term = infer(v, runtime_context)
      -- FIXME: use e_type?
      add_arrays(result_usages, e_usages)
      new_family_args:append(e_term)
    end
    return value.prim_type_type, result_usages, typed_term.prim_user_defined_type_cons(id, new_family_args)
  else
    error("infer: unknown kind: " .. inferrable_term.kind)
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
end

function evaluate(
    typed_term,
    runtime_context
    )
  -- -> a value
  -- TODO: typecheck typed_term and runtime_context?

  if typed_term:is_bound_variable() then
    return runtime_context:get(typed_term:unwrap_bound_variable())
  elseif typed_term:is_literal() then
    return typed_term:unwrap_literal()
  elseif typed_term:is_lambda() then
    return value.closure(typed_term:unwrap_lambda(), runtime_context)
  elseif typed_term:is_qtype() then
    local quantity, t = typed_term:unwrap_qtype()
    local quantity_value = evaluate(quantity, runtime_context)
    local type_value = evaluate(t, runtime_context)
    return value.qtype(quantity_value, type_value)
  elseif typed_term:is_pi() then
    local param_type, param_info, result_type, result_info = typed_term:unwrap_pi()
    local param_type_value = evaluate(param_type, runtime_context)
    local param_info_value = evaluate(param_info, runtime_context)
    local result_type_value = evaluate(result_type, runtime_context)
    local result_info_value = evaluate(result_info, runtime_context)
    return value.pi(param_type_value, param_info_value, result_type_value, result_info_value)
  elseif typed_term:is_application() then
    local f, arg = typed_term:unwrap_application()
    local f_value = evaluate(f, runtime_context)
    local arg_value = evaluate(arg, runtime_context)
    return apply_value(f_value, arg_value)
  elseif typed_term:is_tuple_cons() then
    local elements = typed_term:unwrap_tuple_cons()
    local new_elements = value_array()
    for _, v in ipairs(elements) do
      new_elements:append(evaluate(v, runtime_context))
    end
    return value.tuple_value(new_elements)
  elseif typed_term:is_prim_tuple_cons() then
    local elements = typed_term:unwrap_prim_tuple_cons()
    local new_elements = primitive_value_array()
    local stuck = false
    local stuck_element
    local trailing_values
    for _, v in ipairs(elements) do
      local element_value = evaluate(v, runtime_context)
      if stuck then
        trailing_values:append(element_value)
      elseif element_value:is_prim() then
        new_elements:append(element_value:unwrap_prim())
      elseif element_value:is_neutral() then
        stuck = true
        stuck_element = element_value:unwrap_neutral()
        trailing_values = value_array()
      else
        error("evaluate: trying to apply primitive tuple construction with something that isn't a primitive value")
      end
    end
    if stuck then
      return value.neutral(neutral_value.prim_tuple_stuck(new_elements, stuck_element, trailing_values))
    else
      return value.prim_tuple_value(new_elements)
    end
  elseif typed_term:is_tuple_elim() then
    local mechanism, subject = typed_term:unwrap_tuple_elim()
    local mechanism_value = evaluate(mechanism, runtime_context)
    local subject_value = evaluate(subject, runtime_context)
    if subject_value:is_tuple_value() then
      local subject_elements = subject_value:unwrap_tuple_value()
      local mechacons = mechanism_value
      for _, v in ipairs(subject_elements) do
        mechacons = apply_value(mechacons, v)
      end
      return mechacons
    elseif subject_value:is_prim_tuple_value() then
      local subject_elements = subject_value:unwrap_prim_tuple_value()
      local mechacons = mechanism_value
      for _, v in ipairs(subject_elements) do
        mechacons = apply_value(mechacons, value.prim(v))
      end
      return mechacons
    elseif subject_value:is_neutral() then
      error("nyi")
      local subject_neutral = subject_value:unwrap_neutral()
      local mechacons = mechanism_value
      --for i = ??? do
      --  mechacons = apply_value(mechacons, value.neutral(neutral_value.tuple_element_access_stuck(subject_neutral, i)))
      --end
      return mechacons
    else
      error("evaluate: trying to apply tuple elimination to something that isn't a tuple")
    end
  elseif typed_term:is_operative_cons() then
    return value.operative_value
  elseif typed_term:is_prim_user_defined_type_cons() then
    local id, family_args = typed_term:unwrap_prim_user_defined_type_cons()
    local new_family_args = value_array()
    for _, v in ipairs(family_args) do
      new_family_args:append(evaluate(v, runtime_context))
    end
    return value.prim_user_defined_type(id, new_family_args)
  else
    error("evaluate: unknown kind: " .. typed_term.kind)
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
end

return {
  check = check,
  infer = infer,
  evaluate = evaluate,
}
