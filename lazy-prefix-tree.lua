--local p = require "pretty-print".prettyPrint

local prefix_tree_mt

---@class PrefixTree
---@field kind "ready" | "merge"
---@field hasfinish boolean
---@field finish any?
---@field children { [string] : PrefixTree }
---@field extension PrefixTree?
---@field base PrefixTree?
local PrefixTree = {}

local empty

---@param key string
---@param offset integer?
---@return boolean
---@return any
function PrefixTree:get(key, offset)
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
			if not self.children[c].get then
				p(self)
			end
			return self.children[c]:get(key, offset + 1)
		else
			return false
		end
	end
end

---@return PrefixTree?
function PrefixTree:force()
	if self.kind == "ready" then
		return
	end
	if self.kind ~= "merge" then
		error "trie node in invalid state"
	end
	-- print("forcing tree")
	-- p(self)
	self.children = {}
	self.extension:force()
	self.base:force()
	if not self.base.children then
		print "trying to force broken merger"
		p(self.base)
		print "merging with"
		p(self.extension)
	end
	for k, v in pairs(self.base.children) do
		if self.extension.children[k] then
			self.children[k] = v:extend(self.extension.children[k])
		else
			self.children[k] = v
		end
	end
	for k, v in pairs(self.extension.children) do
		if not self.children[k] then
			self.children[k] = v
		end
	end
	if self.extension.hasfinish then
		self.hasfinish = true
		self.finish = self.extension.finish
	elseif self.base.hasfinish then
		self.hasfinish = true
		self.finish = self.base.finish
	end
	self.extension = nil
	self.base = nil
	self.kind = "ready"
	setmetatable(self, prefix_tree_mt)
	return self
end

---@param other PrefixTree
---@return PrefixTree
function PrefixTree:extend(other)
	if self == nil or other == nil then
		error "can't extend a tree with nil"
	end
	return setmetatable({ kind = "merge", base = self, extension = other }, prefix_tree_mt)
end

---@param key string
---@param value any
---@param offset integer?
---@return PrefixTree
function PrefixTree:put(key, value, offset)
	offset = offset or 1
	self:force()
	local res = {}
	for k, v in pairs(self) do
		res[k] = v
	end
	local children = {}
	for k, v in pairs(self.children) do
		children[k] = v
	end
	res.children = children
	if offset >= #key + 1 then
		res.hasfinish = true
		res.finish = value
		return setmetatable(res, prefix_tree_mt)
	end
	local c = key:sub(offset, offset)
	if not self.children[c] then
		res.children[c] = empty
	end
	res.children[c] = res.children[c]:put(key, value, offset + 1)
	return setmetatable(res, prefix_tree_mt)
end

---@param key string
---@param offset integer?
---@return PrefixTree
function PrefixTree:remove(key, offset)
	offset = offset or 1
	self:force()
	local res = setmetatable({ kind = "ready" }, prefix_tree_mt)
	if offset >= #key + 1 then
		res.finish = nil
		res.hasfinish = false
		res.children = self.children
		return res
	else
		res.finish, res.hasfinish = self.finish, self.hasfinish
	end
	local c = key:sub(offset, offset)
	res.children = {}
	for k, v in pairs(self.children) do
		res.children[k] = v
	end
	if self.children[c] then
		res.children[c] = self.children[c]:remove(key, offset + 1)
		if not res.children[c].hasfinish and not next(res.children[c].children) then
			res.children[c] = nil
		end
	end
	return res
end

---@param fn fun(any): boolean, any
---@return PrefixTree
function PrefixTree:filtermap_values(fn)
	self:force()
	local res = { kind = "ready", children = {} }
	if self.hasfinish then
		res.hasfinish, res.finish = fn(self.finish)
	else
		res.hasfinish = false
	end
	for k, v in pairs(self.children) do
		local child = v:filtermap_values(fn)
		if child.hasfinish or next(child.children) then
			res.children[k] = child
		end
	end
	return setmetatable(res, prefix_tree_mt)
end

local dump_map
prefix_tree_mt = {
	__tostring = function(self)
		return "lazy-prefix-tree" .. dump_map(self)
	end,
	__index = PrefixTree,
}

empty = setmetatable({ kind = "ready", hasfinish = false, children = {} }, prefix_tree_mt)

---@param tab table
---@return PrefixTree
local function build(tab)
	local res = empty
	for k, v in pairs(tab) do
		res = res:put(k, v)
	end
	return res
end

---@param tree PrefixTree
---@param prefix string
---@param dest table
local function extract_map(tree, prefix, dest)
	tree:force()
	if tree.hasfinish then
		dest[prefix] = tree.finish
	end
	for k, v in pairs(tree.children) do
		extract_map(v, prefix .. k, dest)
	end
end

---@param tree PrefixTree
---@return string
function dump_map(tree)
	local content = {}
	extract_map(tree, "", content)
	local components = {}
	for k, v in pairs(content) do
		components[#components + 1] = k .. " = " .. tostring(v)
	end
	if #components == 0 then
		return "{}"
	end
	return "{\n\t" .. table.concat(components, "\n\t") .. "\n}"
end

return {
	empty = empty,
	build = build,
	dump_map = dump_map,
}
