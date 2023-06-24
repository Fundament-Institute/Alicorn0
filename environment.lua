local trie = require './lazy-prefix-tree'

local new_env

local function new_store(val)
  local store = {val = val}
  if is_linear(val.type) then
    store.kind = "useonce"
  else
    store.kind = "reusable"
  end
  return store
end

local environment_mt = {
  __index = {
    get = function(self, name)
      local binding = self.bindings:get(name)
      if binding == nil then
        return false, "symbol " .. name .. " is not in scope"
      end
      if binding.kind == "used" then
        return false, "symbol " .. name .. " was in scope but is a linear value that was already used"
      end
      local val = binding.val
      if binding.kind == "useonce" then
        binding.kind = "used"
        binding.val = nil
      end
      return true, val
    end,
    bind_local = function(self, name, val)
      return new_env {
        locals = self.locals:put(name, new_store(val)),
        nonlocals = self.nonlocals,
        carrier = self.carrier,
        perms = self.perms
      }
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

return {
  new_env = new_env
}
