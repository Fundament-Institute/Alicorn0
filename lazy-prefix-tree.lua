

local prefix_tree_mt
local empty
prefix_tree_mt = {
  __index = {
    get = function(self, key, offset)
      self:force()
      offset = offset or 1
      if offset >= #key + 1 then
        if self.hasfinish then
          return true, self.finish
        else
          return false
        end
      else
        local c = key:sub(offset, offset)
        if self.children[c] then
          return self.children[c]:get(key, offset + 1)
        else
          return false
        end
      end
    end,
    force = function(self)
      if self.kind == "ready" then return end
      if self.kind ~= "merge" then error "trie node in invalid state" end
      self.children = {}
      for k, v in pairs(self.base.children) do
        if self.extend.children[k] then
          self.children[k] = {kind = "merge", base = v, extend = self.extend.children[k]}
        else
          self.children[k] = v
        end
      end
      for k, v in pairs(self.extend.children) do
        if not self.children[k] then
          self.children[k] = v
        end
      end
      if self.extend.hasfinish then
        self.hasfinish = true
        self.finish = self.extend.finish
      elseif self.base.hasfinish then
        self.hasfinish = true
        self.finish = self.base.finish
      end
      self.extend = nil
      self.base = nil
      self.kind = "ready"
      return self
    end,
    extend = function(self, other)
      return setmetatable({kind = "merge", base = self, extend = other}, prefix_tree_mt)
    end,
    put = function(self, key, value, offset)
      offset = offset or 1
      self:force()
      local res = {}
      for k, v in pairs(self) do res[k] = v end
      local children = {}
      for k, v in pairs(self.children) do children[k] = v end
      res.children = children
      if offset >= #key+1 then
        res.hasfinish = true
        res.finish = value
        return setmetatable(res, prefix_tree_mt)
      end
      local c = key:sub(offset, offset)
      if not self.children[c] then res.children[c] = empty end
      res.children[c] = res.children[c]:put(key, value, offset+1)
      return setmetatable(res, prefix_tree_mt)
    end,
    remove = function(self, key, offset)
      offset = offset or 1
      local res = {}
      for k, v in pairs(self) do res[k] = v end
      setmetatable(res, prefix_tree_mt)
      if offset >= #key+1 then
        res.finish = nil
        res.hasfinish = false
        return res
      end
      local c = key:sub(offset, offset)
      if self[c] then
        res[c] = self[c]:remove(key, offset+1)
      end
      return res
    end
  }
}

empty = setmetatable({kind = "ready", hasfinish = false, children = {}}, prefix_tree_mt)

local function build(tab)
  local res = empty
  for k, v in pairs(tab) do
    res = res:put(k, v)
  end
  return res
end

return {
  empty = empty,
  build = build
}
