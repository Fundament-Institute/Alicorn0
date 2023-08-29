local 
trie = require './lazy-prefix-tree'
local types = require './typesystem'
local fibbuf = require './fibonacci-buffer'

local new_env

local function new_store(val)
  local store = {val = val}
  if not types.is_duplicable(val.type) then
    store.kind = "useonce"
  else
    store.kind = "reusable"
  end
  return store
end

local runtime_context_mt

runtime_context_mt = {
  __index = {
    get = function(self, index) 
      return self.bindings:get(index)
    end,
    append = function(self, value) 
      local copy = { bindings = self.bindings:append(value) }
      return setmetatable(copy, runtime_context_mt)
    end
  }
}


local function runtime_context()
  local self = {}
  self.bindings = fibbuf()
  return setmetatable(self, runtime_context_mt)
end

local typechecking_context_mt

typechecking_context_mt = {
  __index = {
    get_name = function(self, index) 
      return self.bindings:get(index).name
    end,
    get_type = function(self, index)
      return self.bindings:get(index).type
    end,
    append = function(self, name, type) 
      local copy = { bindings = self.bindings:append({name = name, type = type}) }
      return setmetatable(copy, typechecking_context_mt)
    end
  }
}

local function typechecking_context()
  local self = {}
  self.bindings = fibbuf()
  return setmetatable(self, typechecking_context_mt)
end

-- empty for now, just used to mark the table
local module_mt = {}

local environment_mt = {
  __index = {
    get = function(self, name)
      local present, binding = self.bindings:get(name)
      if not present then return false, "symbol \"" .. name .. "\" is not in scope" end
      if binding == nil then
        return false, "symbol \"" .. name .. "\" is marked as present but with no data; this indicates a bug in the environment or something violating encapsulation"
      end
      return true, binding
    end,
    bind_local = function(self, name, term)
      return new_env {
        locals = self.locals:put(name, term),
        nonlocals = self.nonlocals,
        carrier = self.carrier,
        perms = self.perms
      }
    end,
    gather_module = function(self)
      return self, setmetatable({bindings = self.locals}, module_mt)
    end,
    open_module = function(self, module)
      return new_env {
        locals = self.locals:extend(module.bindings),
        nonlocals = self.nonlocals,
        carrier = self.carrier,
        perms = self.perms
      }
    end,
    use_module = function(self, module)
      return new_env {
        locals = self.locals,
        nonlocals = self.nonlocals:extend(module.bindings),
        carrier = self.carrier,
        perms = self.perms
      }
    end,
    unlet_local = function(self, name)
      return new_env {
        locals = self.locals:remove(name),
        nonlocals = self.nonlocals,
        carrier = self.carrier,
        perms = self.perms
      }
    end,
    enter_block = function(self)
      return { shadowed = self }, new_env {
        locals = nil,
        nonlocals = self.nonlocals:extend(self.locals),
        carrier = self.carrier,
        perms = self.perms
      }
    end,
    exit_block = function(self, term, shadowed)
      for k, v in pairs(self.locals) do
        term:let(k, v)
      end
    end,
    child_scope = function(self)
      return new_env {
        locals = trie.empty,
        nonlocals = self.bindings,
        carrier = self.carrier,
        perms = self.perms
      }
    end,
    exit_child_scope = function(self, child)
      return new_env {
        locals = self.locals,
        nonlocals = self.nonlocals,
        carrier = child.carrier,
        perms = self.perms
      }
    end,
    get_carrier = function(self)
      if self.carrier == nil then
        return false, "The environment has no effect carrier, code in the environment must be pure"
      end
      if self.carrier.kind == "used" then
        return false, "The environment used to have an effect carrier but it was used; this environment shouldn't be used for anything and this message indicates a linearity-violating bug in an operative"
      end
      local val = self.carrier.val
      if self.carrier.kind == "useonce" then
        self.carrier.val = nil
        self.carrier.kind = "used"
      end
      return true, val
    end,
    provide_carrier = function(self, carrier)
      return new_env {
        locals = self.locals,
        nonlocals = self.nonlocals,
        carrier = new_store(carrier),
        perms = self.perms
      }
    end
  }
}

function new_env(opts)
  local self = {}
  self.locals = opts.locals or trie.empty
  self.nonlocals = opts.nonlocals or trie.empty
  self.bindings = self.nonlocals:extend(self.locals)
  self.carrier = opts.carrier or nil
  self.perms = opts.perms or {}
  return setmetatable(self, environment_mt)
end

local function dump_env(env)
  return "Environment"
    .. "\nlocals: " .. trie.dump_map(env.locals)
    .. "\nnonlocals: " .. trie.dump_map(env.nonlocals)
    .. "\ncarrier: " .. tostring(env.carrier)
end

local gen = require './terms-generators'
local runtime_context_type = gen.declare_foreign(gen.metatable_equality(runtime_context_mt))
local typechecking_context_type = gen.declare_foreign(gen.metatable_equality(typechecking_context_mt))
local environment_type = gen.declare_foreign(gen.metatable_equality(environment_mt))

return {
  new_env = new_env,
  dump_env = dump_env,
  new_store = new_store,
  runtime_context = runtime_context,
  typechecking_context = typechecking_context,
  runtime_context_type = runtime_context_type,
  typechecking_context_type = typechecking_context_type,
  environment_type = environment_type,
}
