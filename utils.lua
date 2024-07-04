local M = {}

---@param ... any
---@return table
function M.concat(...)
	local res = {}
	local inputs = { ... }
	for _, tab in ipairs(inputs) do
		for _, elem in ipairs(tab) do
			table.insert(res, elem)
		end
	end
	return res
end

---Exists only to prevent tail call optimizations
---@param ... any
---@return ...
function M.notail(...)
	return ...
end

--- name and info aren't used here because they're inspected by the stacktrace using the debug API if an error occurs
---@param name string
---@param info any
---@param fn fun(...) : ...
---@param ... any
---@return ...
function M.tag(name, info, fn, ...)
	return M.notail(fn(...))
end

--[[
--- len that starts counting from something other than 1 using binary search
---@param list any[]
local function dynlen(list, start)
	if list[start] == nil then
		return 0
	end
	local front = start
	local back = start + 1
	while rawget(list, back) ~= nil do
		back = back * 2
	end
	local mid = (front + back) / 2
	while mid ~= front do
		if rawget(list, mid) ~= nil then
			front = mid + 1
		else
			back = mid
		end

		mid = (front + back) / 2
	end
	if rawget(list, front) == nil then
		return front - start
	end
	return front - start + 1
end]]

---Insert an element into a list, respecting whether it was a shadowed array or not
---@generic T
---@param list T[]
---@param value T
function M.append(list, value)
	-- If this is a shadowed array it'll trigger the __newindex overload that increments length
	list[#list + 1] = value
end

-- This is a metatable that shadows an array, but only if you use shadowinsert
local shadowarray_mt = {
	__index = function(t, k)
		return t.__shadow[k]
	end,
	__newindex = function(t, k, v)
		if k == #t + 1 then
			t.__length = t.__length + 1
		end
		rawset(t, k, v)
	end,
	__len = function(t)
		return #t.__shadow + t.__length
	end,
	__ipairs = function(tbl)
		return function(t, i)
			i = i + 1
			local v = t[i]
			if nil ~= v then
				return i, v
			end
		end, tbl, 0
	end,
}

-- This is a metatable that shadows a dictionary, pretending to have all of it's elements without actually affecting it
local shadowtable_mt = {
	__index = function(t, k)
		return t.__shadow[k]
	end,
	__pairs = function(t)
		local function shadow_iter(t, k)
			local result, v = nil, nil
			if k == nil or t.__shadow[k] ~= nil then
				result, v = next(t.__shadow, k)
			end
			if result == nil then
				-- If k existed in __shadow but next returns nil, that was the end of the table, so restart with nil
				if t.__shadow[k] ~= nil then
					k = nil
				end
				result, v = next(t, k)
			end
			return result, v
		end

		-- Return an iterator function, the table, starting point
		return shadow_iter, t, nil
	end,
}

---@generic T : table
---@param t T
---@return T
function M.shadowtable(t)
	return setmetatable({ __shadow = t }, shadowtable_mt)
end

---@generic T
---@param t T[] | { [integer]: T, __length: integer }
---@return { [integer]: T, __length: integer }
function M.shadowarray(t)
	return setmetatable({ __shadow = t, __length = 0 }, shadowarray_mt)
end

---Given a shadowed table, flattens its values on to the shadowed table below and returns it
---@generic T : table
---@param t T
---@return T
function M.commit(t)
	setmetatable(t, nil)
	local original = t.__shadow
	t.__shadow = nil
	t.__length = nil
	for k, v in pairs(t) do
		rawset(original, k, v)
	end
	return original
end

---@generic T : table
---@param src T
---@return T
function M.shallow_copy(src)
	local t = {}
	for k, v in pairs(src) do
		t[k] = v
	end
	return t
end

return M
