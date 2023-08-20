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

local gen = require './terms-generators'

local function getmvinfo(id, mvs)
  if mvs == nil then
    return
  end
  -- if this is slow fixme later
  return mvs[id] or getmvinfo(id, mvs.prev_mvs)
end

local unify
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
        value = unify(canonical_info.bound_value, value)
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
  },
  value_check = gen.metatable_equality,
}

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

local builtin_number = gen.declare_foreign(function(val)
  return type(val) == "number"
end)

local typed = gen.declare_type()
local value = gen.declare_type()
local checkable = gen.declare_type()
local inferrable = gen.declare_type()
-- checkable terms need a target type to typecheck against
checkable:define_enum("checkable", {
  {"inferred", {"inferred_term", inferrable}},
  {"lambda", {"body", checkable}},
})
-- inferrable terms can have their type inferred / don't need a target type
inferrable:define_enum("inferrable", {
  {"level_type"},
  {"level0"},
  {"level_suc", {"previous_level", inferrable}},
  {"level_max", {
    "level_a", inferrable,
    "level_b", inferrable,
  }},
  {"star"},
  {"prop"},
  {"prim"},
  {"annotated", {
    "annotated_term", checkable,
    "annotated_type", inferrable,
  }},
  {"typed", {
     "type", value,
     "typed_term", typed,
  }},
})
-- typed terms have been typechecked but do not store their type internally
typed:define_enum("typed", {
  {"lambda", {"body", typed}},
  {"level_type"},
  {"level0"},
  {"level_suc", {"previous_level", typed}},
  {"level_max", {
    "level_a", typed,
    "level_b", typed,
  }},
  {"star", {"level", builtin_number}},
  {"prop", {"level", builtin_number}},
  {"prim"},
  {"literal", {"literal_value", value}},
})

local free = gen.declare_enum("free", {
  {"metavariable", {"metavariable", metavariable_mt}},
  -- TODO: quoting and axiom
})

local quantity = gen.declare_enum("quantity", {
  {"erased"},
  {"linear"},
  {"unrestricted"},
})
local visibility = gen.declare_enum("visibility", {
  {"explicit"},
  {"implicit"},
})
local purity = gen.declare_enum("purity", {
  {"effectful"},
  {"pure"},
})
local resultinfo = gen.declare_record("resultinfo", {"purity", purity})
value:define_enum("value", {
  -- erased, linear, unrestricted / none, one, many
  {"quantity", {"quantity", quantity}},
  -- explicit, implicit,
  {"visibility", {"visibility", visibility}},
  -- info about the argument (is it implicit / what are the usage restrictions?)
  -- quantity/visibility should be restricted to free or (quantity/visibility) rather than any value
  {"arginfo", {"quantity", value, "visibility", value}},
  -- whether or not a function is effectful /
  -- for a function returning a monad do i have to be called in an effectful context or am i pure
  {"resultinfo", {"resultinfo", resultinfo}},
  {"pi", {
    "argtype", value,
    "arginfo", value,
    "resulttype", value,
    "resultinfo", resultinfo
  }},
  -- closure is a type that contains a typed term corresponding to the body
  -- and a runtime context representng the bound context where the closure was created
  {"closure", {}}, -- TODO
  {"level_type"},
  {"number_type"},
  {"number", {"number", builtin_number}},
  {"level", {"level", builtin_number}},
  {"star", {"level", builtin_number}},
  {"prop", {"level", builtin_number}},
  {"prim"},
})

local function discard_self(fn)
  return function(self, ...)
    return fn(...)
  end
end

-- fn(free_value) and table of functions eg free.metavariable(metavariable)
value.free = setmetatable({}, {
    __call = discard_self(gen.gen_record(value, "value_free", {"free_value", free})) -- value should be constructed w/ free.something()
})
value.free.metavariable = function(mv)
  return value.free(free.metavariable(mv))
end

local function extract_value_metavariable(value) -- -> Option<metavariable>
  if value.kind == "value_free" and value.free_value.kind == "free_metavariable" then
    return value.free_value.metavariable
  end
  return nil
end

unify = function(
    first_value,
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

  local unified = {}
  local prefer_left = true
  local prefer_right = true
  for _, v in ipairs(first_value.params) do
    local first_arg = first_value[v]
    local second_arg = second_value[v]
    if first_arg.kind then
      local u = unify(first_arg, second_arg)
      unified[v] = u
      prefer_left = prefer_left and u == first_arg
      prefer_right = prefer_right and u == second_arg
    elseif first_arg ~= second_arg then
      p("unify args", first_value, second_value)
      error("unification failure as " .. v .. " field value doesn't match")
    end
  end

  if prefer_left then
    return first_value
  elseif prefer_right then
    return second_value
  else
    unified.kind = first_value.kind
    unified.params = first_value.params
    return unified
  end
end

local function check(
    checkable_term, -- constructed from checkable
    typechecking_context, -- todo
    target_type) -- must be unify with target type (there is some way we can assign metavariables to make them equal)
  -- -> type of that term, a typed term

  if checkable_term.kind == "inferred" then
    local inferred_type, typed_term = infer(checkable_term.inferred_term, typechecking_context)
    unified_type = unify(inferred_type, target_type) -- can fail, will cause lua error
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
    return value.level_type, typed.level0
  elseif inferrable_term.kind == "inferrable_level_suc" then
    local arg_type, arg_term = infer(inferrable_term.previous_level, typechecking_context)
    unify(arg_type, value.level_type)
    return value.level_type, typed.level_suc(arg_term)
  elseif inferrable_term.kind == "inferrable_level_max" then
    local arg_type_a, arg_term_a = infer(inferrable_term.level_a, typechecking_context)
    local arg_type_b, arg_term_b = infer(inferrable_term.level_b, typechecking_context)
    unify(arg_type_a, value.level_type)
    unify(arg_type_b, value.level_type)
    return value.level_type, typed.level_max(arg_term_a, arg_term_b)
  elseif inferrable_term.kind == "inferrable_level_type" then
    return value.star(0), typed.level_type
  elseif inferrable_term.kind == "inferrable_star" then
    return value.star(1), typed.star(0)
  elseif inferrable_term.kind == "inferrable_prop" then
    return value.star(1), typed.prop(0)
  elseif inferrable_term.kind == "inferrable_prim" then
    return value.star(1), typed.prim
  end

  error("unknown kind in infer: " .. inferrable_term.kind)
end

local function evaluate(
    typed_term,
    runtime_context
    )
  -- -> a value

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

  error("unknown kind in evaluate " .. typed_term.kind)
end

return {
  checkable = checkable, -- {}
  inferrable = inferrable, -- {}
  check = check, -- fn
  infer = infer, -- fn
  typed = typed, -- {}
  evaluate = evaluate, -- fn
  types = types, -- {}
  unify = unify, -- fn
  typechecker_state = typechecker_state, -- fn (constructor)

  quantity = quantity,
  visibility = visibility,
  arginfo = arginfo,
  purity = purity,
  resultinfo = resultinfo,
  value = value,
}
