local trie = require './lazy-prefix-tree'

local new_env

local environment_mt = {
  __index = {
    get = function(self, name)
      return self.bindings:get(name)
    end,
    bind_local = function(self, name, val)
      return new_env {
        locals = self.locals:put(name, val),
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

  }
}

function new_env(opts)
  local self = {}
  self.locals = opts.locals or trie.empty
  self.nonlocals = opts.nonlocals or trie.empty
  self.bindings = self.nonlocals:extend(self.locals)
  self.carrier = opts.carrier or nil
  return setmetatable(self, environment_mt)
end

return {
  new_env = new_env
}
