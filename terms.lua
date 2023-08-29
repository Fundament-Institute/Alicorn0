-- provide ways to construct all terms
-- checker untyped term and typechecking context -> typed term
-- evaluator takes typed term and runtime context -> value

-- type checker monad
-- error handling and metavariable unification facilities
--
-- typechecker is allowed to fail, typechecker monad carries failures upwards
--   for now fail fast, but design should vaguely support multiple failures

-- metavariable unification
--   a metavariable is like a variable butmore meta
--   create a set of variables -> feed into code -> evaluate with respect to them
--   in order for the values produced by these two invocations to be the same, what would the metavariales need to be bound to?
--   (this is like symbolic execution)
--
-- in the typechecking monad we create a metavariable which takes a type and produces a term or value of that type and
-- we can unfy two values against each other to solve their metavariables or it can fail
-- for now unification with equality is the only kind of constraint. eventuall may be others but that's hard/no need right now

-- we will use lua errors for handling here - use if, error not assert so JIT understands
-- metavariables = table, edit the table, this is the stateful bit the monad has
-- methods on metavariable that bind equal to some value, if it is already bound it has to unify which can fail, failure cascades
-- thing passed to bind equl method on metavariable is a 'value' - enumerated datatype, like term but less cases
--   scaffolding - need to add cases here foreach new value variant
--
-- create metavariable, pass in as arg to lambda, get back result, unify against another type
--   it's ok if a metavariable never gets constrained during part of typechecking
-- give metavariables sequential ids (tracked in typechecker_state)

-- metavariable state transitions, can skip steps but must always move down

-- unbound
-- vvv
-- bound to exactly another metavariable - have a reference to a metavariable
-- vvv
-- bound to a value - have a reference to a value

-- when binding to another metavariable bind the one with a greater index to the lesser index

local environment = require './environment'
local metalang = require './metalanguage'

local gen = require './terms-generators'
local map = gen.declare_map
local array = gen.declare_array

local function getmvinfo(id, mvs)
  if mvs == nil then
    return
  end
  -- if this is slow fixme later
  return mvs[id] or getmvinfo(id, mvs.prev_mvs)
end

local metavariable_mt

metavariable_mt = {
  __index = {
    get_value = function(self)
      local canonical = self:get_canonical()
      local canonical_info = getmvinfo(canonical.id, self.typechecker_state.mvs)
      return canonical_info.bound_value or values.free(free.metavariable(canonical))
    end,
    get_canonical = function(self)
      local canonical_id = self.typechecker_state:get_canonical_id(self.id)

      if canonical_id ~= self.id then
        return setmetatable({
            id = canonical_id,
            typechecker_state = self.typechecker_state,
                            }, metavariable_mt):get_canonical()
      end

      return self
    end,
    -- this gets called to bind to any value that isn't another metavariable
    bind_value = function(self, value)
      -- FIXME: if value is a metavariable (free w/ metavariable) call bind_metavariable here?
      local canonical = self:get_canonical()
      local canonical_info = getmvinfo(canonical.id, self.typechecker_state.mvs)
      if canonical_info.bound_value and canonical_info.bound_value ~= value then
        -- unify the two values, throws lua error if can't
        value = canonical_info.bound_value:unify(value)
      end
      self.typechecker_state.mvs[canonical.id] = {
        bound_value = value,
      }
      return value
    end,
    bind_metavariable = function(self, other)
      if self == other then
        return
      end

      if getmetatable(other) ~= metavariable_mt then
        p(self, other, getmetatable(self), getmetatable(other))
        error("metavariable.bind should only be called with metavariable as arg")
      end

      if self.typechecker_state ~= other.typechecker_state then
        error("trying to mix metavariables from different typechecker_states")
      end

      if self.id == other.id then
        return
      end

      if self.id < other.id then
        return other:bind_metavariable(self)
      end

      local this = getmvinfo(self.id, self.typechecker_state.mvs)
      if this.bound_value then
        error("metavariable is already bound to a value")
      end

      self.typechecker_state.mvs[self.id] = {
        bound_mv_id = other.id,
      }
    end
  }
}
local metavariable_type = gen.declare_foreign(gen.metatable_equality(metavariable_mt))

local typechecker_state_mt
typechecker_state_mt = {
  __index = {
    metavariable = function(self) -- -> metavariable instance
      self.next_metavariable_id = self.next_metavariable_id + 1
      self.mvs[self.next_metavariable_id] = {}
      return setmetatable(
        {
          id = self.next_metavariable_id,
          typechecker_state = self,
        }, metavariable_mt)
    end,
    get_canonical_id = function(self, mv_id) -- -> number
      local mvinfo = getmvinfo(mv_id, self.mvs)
      if mvinfo.bound_mv_id then
        local final_id = self:get_canonical_id(mvinfo.bound_mv_id)
        if final_id ~= mvinfo.bound_mv_id then
          -- ok to mutate rather than setting in self.mvs here as collapsing chain is idempotent
          mvinfo.bound_mv_id = final_id
        end
        return final_id
      end
      return mv_id
    end,
  }
}

local function typechecker_state()
  return setmetatable({
      next_metavariable_id = 0,
      mvs = { prev_mvs = nil },
    }, typechecker_state_mt)
end

-- freeze and then commit or revert
-- like a transaction
local function speculate(f, ...)
  mvs = {
    prev_mvs = mvs,
  }
  local commit, result = f(...)
  if commit then
    -- commit
    for k, v in pairs(mvs) do
      if k ~= "prev_mvs" then
        prev_mvs[k] = mvs[k]
      end
    end
    mvs = mvs.prev_mvs
    return result
  else
    -- revert
    mvs = mvs.prev_mvs
    -- intentionally don't return result if set if not committing to prevent smuggling out of execution
    return nil
  end
end

local checkable_term = gen.declare_type()
local inferrable_term = gen.declare_type()
local typed_term = gen.declare_type()
local value = gen.declare_type()
local neutral_value = gen.declare_type()
-- checkable terms need a target type to typecheck against
checkable_term:define_enum("checkable", {
  {"inferred", {"inferred_term", inferrable_term}},
  {"lambda", {"body", checkable_term}},
})
-- inferrable terms can have their type inferred / don't need a target type
inferrable_term:define_enum("inferrable", {
  {"level_type"},
  {"level0"},
  {"level_suc", {"previous_level", inferrable_term}},
  {"level_max", {
    "level_a", inferrable_term,
    "level_b", inferrable_term,
  }},
  {"star"},
  {"prop"},
  {"prim"},
  {"annotated", {
    "annotated_term", checkable_term,
    "annotated_type", inferrable_term,
  }},
  {"typed", {
     "type", value,
     "typed_term", typed_term,
  }},
})
-- typed terms have been typechecked but do not store their type internally
typed_term:define_enum("typed", {
  {"bound_variable", {"index", gen.builtin_number}},
  {"literal", {"literal_value", value}},
  {"lambda", {"body", typed_term}},
  {"qtype", {"quantity", typed_term, "type", typed_term}},
  {"pi", {
    "arg_type", typed_term,
    "arg_info", typed_term,
    "result_type", typed_term,
    "result_info", typed_term,
  }},
  {"application", {
    "f", typed_term,
    "param", typed_term,
  }},
  {"level_type"},
  {"level0"},
  {"level_suc", {"previous_level", typed_term}},
  {"level_max", {
    "level_a", typed_term,
    "level_b", typed_term,
  }},
  {"star", {"level", gen.builtin_number}},
  {"prop", {"level", gen.builtin_number}},
  {"prim"},
  {"record_cons", {"fields", map(gen.builtin_string, typed_term)}},
  {"record_extend", {"base", typed_term, "fields", map(gen.builtin_string, typed_term)}},
  {"data_cons", {"constructor", gen.builtin_string, "arg", typed_term}},
  {"data_elim", {"motive", typed_term, "mechanism", typed_term, "subject", typed_term}},
  {"data_rec_elim", {"motive", typed_term, "mechanism", typed_term, "subject", typed_term}},
  {"object_cons", {"methods", map(gen.builtin_string, typed_term)}},
  {"object_corec_cons", {"methods", map(gen.builtin_string, typed_term)}},
  {"object_elim", {"motive", typed_term, "mechanism", typed_term, "subject", typed_term}},
})

local free = gen.declare_enum("free", {
  {"metavariable", {"metavariable", metavariable_type}},
  -- TODO: quoting and axiom
})

-- erased - - - - never used at runtime
--              - can only be placed in other erased slots
--              - e.g. the type Array(u8, 42) has length information that is relevant for typechecking
--              -      but not for runtime. the constructor of Array(u8, 42) marks the 42 as erased,
--              -      and it's dropped after compile time.
-- linear - - - - used once during runtime
--              - e.g. world
-- unrestricted - used arbitrarily many times during runtime
local quantity = gen.declare_enum("quantity", {
  {"erased"},
  {"linear"},
  {"unrestricted"},
})
-- implicit arguments are filled in through unification
-- e.g. fn append(t : star(0), n : nat, xs : Array(t, n), val : t) -> Array(t, n+1)
--      t and n can be implicit, given the explicit argument xs, as they're filled in by unification
local visibility = gen.declare_enum("visibility", {
  {"explicit"},
  {"implicit"},
})
-- whether a function is effectful or pure
-- an effectful function must return a monad
-- calling an effectful function implicitly inserts a monad bind between the
-- function return and getting the result of the call
local purity = gen.declare_enum("purity", {
  {"effectful"},
  {"pure"},
})
local result_info = gen.declare_record("result_info", {"purity", purity})

-- values must always be constructed in their simplest form, that cannot be reduced further.
-- their format must enforce this invariant.
-- e.g. it must be impossible to construct "2 + 2"; it should be constructed in reduced form "4".
-- values can contain neutral values, which represent free variables and stuck operations.
-- stuck operations are those that are blocked from further evaluation by a neutral value.
-- therefore neutral values must always contain another neutral value or a free variable.
-- their format must enforce this invariant.
-- e.g. it's possible to construct the neutral value "x + 2"; "2" is not neutral, but "x" is.
-- values must all be finite in size and must not have loops.
-- i.e. destructuring values always (eventually) terminates.
value:define_enum("value", {
  -- erased, linear, unrestricted / none, one, many
  {"quantity", {"quantity", quantity}},
  -- explicit, implicit,
  {"visibility", {"visibility", visibility}},
  -- a type with a quantity
  {"qtype", {"quantity", value, "type", value}},
  -- info about the argument (is it implicit / what are the usage restrictions?)
  -- quantity/visibility should be restricted to free or (quantity/visibility) rather than any value
  {"arg_info", {"visibility", value}},
  -- whether or not a function is effectful /
  -- for a function returning a monad do i have to be called in an effectful context or am i pure
  {"result_info", {"result_info", result_info}},
  {"pi", {
    "arg_type", value, -- qtype
    "arg_info", value, -- arginfo
    "result_type", value, -- qtype
    "result_info", value, -- result_info
  }},
  -- closure is a type that contains a typed term corresponding to the body
  -- and a runtime context representng the bound context where the closure was created
  {"closure", {"code", typed_term, "capture", environment.runtime_context_type}},

  -- metaprogramming stuff
  -- TODO: add types of terms, and type indices
  {"syntax_value", {"syntax", metalang.constructed_syntax_type}},
  {"syntax_type"},
  {"matcher_value", {"matcher", metalang.matcher_type}},
  {"matcher_type", {"result_type", value}},
  {"reducer_value", {"reducer", metalang.reducer_type}},
  {"environment_value", {"environment", environment.environment_type}},
  {"environment_type"},
  {"checkable_term", {"checkable_term", checkable_term}},
  {"inferrable_term", {"inferrable_term", inferrable_term}},
  {"typed_term", {"typed_term", typed_term}},
  --{"typechecker_monad_value", }, -- TODO
  {"typechecker_monad_type", {"wrapped_type", value}},
  {"name_type"},
  {"name", {"name", gen.builtin_string}},

  -- ordinary data
  {"tuple_value", {"elements", array(value)}},
  {"tuple_type", {"decls", value}},
  {"data_value", {"constructor", gen.builtin_string, "arg", value}},
  {"data_type", {"decls", value}},
  {"record_value", {"fields", map(gen.builtin_string, value)}},
  {"record_type", {"decls", value}},
  {"record_extend_stuck", {"base", neutral_value, "extension", map(gen.builtin_string, value)}},
  {"object_value", {"methods", map(gen.builtin_string, value)}},
  {"object_type", {"decls", value}},
  {"level_type"},
  {"number_type"},
  {"number", {"number", gen.builtin_number}},
  {"level", {"level", gen.builtin_number}},
  {"star", {"level", gen.builtin_number}},
  {"prop", {"level", gen.builtin_number}},
  {"prim"},

  {"neutral", {"neutral", neutral_value}},
})

neutral_value:define_enum("neutral_value", {
  -- fn(free_value) and table of functions eg free.metavariable(metavariable)
  -- value should be constructed w/ free.something()
  {"free", {"free", free}},
  {"application_stuck", {"f", neutral_value, "param", value}},
  {"data_elim_stuck", {"motive", value, "handler", value, "subject", neutral_value}},
  {"data_rec_elim_stuck", {"motive", value, "handler", value, "subject", neutral_value}},
  {"object_elim_stuck", {"motive", value, "method", value, "subject", neutral_value}},
  {"record_elim_stuck", {"motive", value, "fields", value, "uncurried", value, "subject", neutral_value}},
  --{"tuple_elim_stuck", {}},
})

neutral_value.free.metavariable = function(mv)
  return neutral_value.free(free.metavariable(mv))
end

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

  error("unknown kind in check: " .. checkable_term.kind)
end

local function infer(
    inferrable_term, -- constructed from inferrable
    typechecking_context -- todo
    )
  -- -> type of term, a typed term,
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

  error("unknown kind in infer: " .. inferrable_term.kind)
end

local function evaluate(
    typed_term,
    runtime_context
    )
  -- -> a value

  if typed_term.kind == "typed_bound_variable" then
    return runtime_context:get(typed_term.index)
  elseif typed_term.kind == "typed_literal" then
    return typed_term.literal_value
  elseif typed_term.kind == "typed_lambda" then
    local value = value.closure(typed_term.body, runtime_context)
    return value
  elseif typed_term.kind == "typed_qtype" then
    local eval_quantity = evaluate(typed_term.quantity, runtime_context)
    local eval_type = evaluate(typed_term.type, runtime_context)
    return value.qtype(eval_quantity, eval_type)
  elseif typed_term.kind == "typed_pi" then
    local eval_arg_type = evaluate(typed_term.arg_type, runtime_context)
    local eval_arg_info = evaluate(typed_term.arg_info, runtime_context)
    local eval_result_type = evaluate(typed_term.result_type, runtime_context)
    local eval_result_info = evaluate(typed_term.result_info, runtime_context)
    return value.pi(eval_arg_type, eval_arg_info, eval_result_type, eval_result_info)
  elseif typed_term.kind == "typed_application" then
    local eval_f = evaluate(typed_term.f, runtime_context)
    local eval_param = evaluate(typed_term.param, runtime_context)
    if eval_f.kind == "value_closure" then
      local inner_context = eval_f.capture:append(eval_param)
      return evaluate(eval_f.code, inner_context)
    elseif eval_f.kind == "value_neutral" then
      return value.neutral(neutral_value.application_stuck(eval_f.neutral_value, eval_param))
    else
      error("trying to apply on something that isn't a function/closure")
    end

  elseif typed_term.kind == "typed_level0" then
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

  error("unknown kind in evaluate " .. typed_term.kind)
end

return {
  checkable_term = checkable_term, -- {}
  inferrable_term = inferrable_term, -- {}
  check = check, -- fn
  infer = infer, -- fn
  typed_term = typed_term, -- {}
  evaluate = evaluate, -- fn
  types = types, -- {}
  typechecker_state = typechecker_state, -- fn (constructor)

  quantity = quantity,
  visibility = visibility,
  arginfo = arginfo,
  purity = purity,
  resultinfo = resultinfo,
  value = value,
  neutral_value = neutral_value,
}
