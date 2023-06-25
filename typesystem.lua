

-- typeclass : tuple a -> constraint
--

-- indexed sum type
-- parameters may appear in fields that don't
-- indexed product type
-- indexed codata type
--
--

-- A type must be one of
-- - A parameterized kind
-- - A type family invocation
-- - A recursion operator
--
-- A parameterized kind is represented

local p = require 'pretty-print'.prettyPrint

local hasfixedlayout = {}

local typeerror_mt = {
  __tostring = function(self)
    local message = self.text
    if self.cause then
      message = message .. " because:\n" .. tostring(self.cause)
    end
    return message
  end
}

local typeerror = {
  kind_mismatch = function(a, b)
    return {
      text = "kind " .. a .. " doesn't match kind " .. b,
      cause = nil
    }
  end,
  param_notidentical = function(kind, idx, cause)
    return {
      text = "parameters of " .. kind .. " weren't identical at position " .. idx,
      cause = cause
    }
  end,
  param_length = function(kind, len_a, len_b, cause)
    return {
      text = "parameters of " .. kind .. " were of different lengths " .. len_a .. " and " .. len_b,
      cause = cause
    }
  end,
  unification_failed = function(idx, cause)
    return {
      text = "unification required the types at pattern variable " .. idx .. " to match, but they did not",
      cause = cause
    }
  end,
  unrealized_trait = function()
    return {
      text = "the trait required doesn't exist on the specified type"
    }
  end
}

for k, v in pairs(typeerror) do
  typeerror[k] = function(...) return setmetatable(v(...), typeerror_mt) end
end

local function typeident(a, b)
  -- print "checking type identity"
  -- p(a)
  -- p(b)
  if a.kind ~= b.kind then
    return false, typeerror.kind_mismatch(a.kind, b.kind)
  end
  if #a.params ~= #b.params then
    -- error "two types were provided different length parameterizations, which is illegal"
    -- TODO: make this properly typed again; temporary workaround for tuples until indexed types can be reintroduced
    return false, typeerror.param_length(a.kind, #a.params, #b.params)
  end
  for i = 1, #a.params do
    local ok, err = typeident(a.params[i], b.params[i])
    if not ok then
      return false, typeerror.param_notidentical(a.kind, i, err)
    end
  end
  return true
end

local function typepat(quantmatch, pattern, subject)
  if subject.kind ~= inputpattern.kind then
    return false, typeerror.kind_mismatch(subject.kind, inputpattern.kind)
  end
  for i, patarg in ipairs(inputpattern.params) do
    if patarg.kind == "variable" then
      if quantmatch[patarg.idx] then
        local ok, err = typeident(quantmatch[patarg.idx], subject.params[i])
        if not ok then
          return false, typeerror.unification_failed(i, err)
        end
      end
    elseif patarg.kind == "pattern" then
      local ok, err = typepat(quantmatch, patarg.pat, subject.params[i])
      if not ok then return false, err end
    end
  end
  return true
end

local function realize_typepat(quantmatch, pattern)
  local res = {kind = pattern.kind, params = {}}
  for i, patarg in ipairs(pattern.params) do
    if patarg.kind == "variable" then
      res[i] = quantmatch[patarg.idx]
    elseif patarg.kind == "pattern" then
      res[i] = realize_typepat(quantmatch, pattern)
    end
  end
  return res
end

local function typematch_args(quantifications, inputpattern, subject, outputpattern)
  local quantmatch = {}
  local ok, err = typepat(quantmatch, inputpattern, subject)
  if not ok then return false, err end
  return true, realize_typepat(quantmatch, outputpattern)
end

local function realize_trait(trait, subject)
  for _, matcher in ipairs(trait.matchers) do
    local quantmatch = {}
    local ok, err = typepat(quantmatch, inputpattern, subject)
    error "NYI"
  end
end

-- TODO: extend the kind system to have wrapper types and computed properties

local number = {kind = "number", params = {}}
local string = {kind = "string", params = {}}
local function primap(arg, res)
  return {kind = "primap", params = {arg, res}}
end
local function tuple(fields)
  return {kind = "tuple", params = fields}
  --TODO: make this store types as an immutable sequence type
end
local primop = {kind = "primop", params = {}}

local environment = {kind = "environment", params = {}}
local anyval = {kind = "anyval", params = {}}

--TODO: fix type in type bug
local type = {kind = "type", params = {}}

local nonlinear_kinds = {
  number = true,
  string = true,
  primap = true,
  tuple = true,
  primop = true,
  environment = false,
  anyval = false,
  type = true,
}
local function is_linear(t)
  return not nonlinear_kinds[t.kind]
end

return {
  number = number,
  string = string,
  primap = primap,
  primop = primop,
  tuple = tuple,
  environment = environment,
  anyval = anyval,
  type = type,
  is_linear = is_linear,
  typeident = typeident,
  typepat = typepat,
  realize_typepat = realize_typepat,
  typematch_args = typematch_args
}
