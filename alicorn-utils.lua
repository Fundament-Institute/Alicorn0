local M = {}

function M.numerify(...)
	return select("#", ...), ...
end

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
	if rawget(list, "__lock") then
		error("Modifying a shadowed object! This should never happen!")
	end

	-- If this is a shadowed array it'll trigger the __newindex overload that increments length
	list[#list + 1] = value

	--[[for i = 1, #list do
		if list[i] == nil then
			print("found hole:" .. M.dumptable(list))
			os.exit(-1)
		end
	end]]
end

---Removes an element from a list, respecting whether it was a shadowed array or not
---@generic T
---@param list T[] | { [integer]: T, __length : integer }
---@return T
function M.pop(list)
	if rawget(list, "__lock") then
		error("Modifying a shadowed object! This should never happen!")
	end

	local value = list[#list]
	rawset(list, #list, nil)
	if rawget(list, "__length") then
		rawset(list, "__length", rawget(list, "__length") - 1)
	end
	return value
end

-- This is a metatable that shadows an array, but only if you use shadowinsert
local shadowarray_mt = {
	__index = function(t, k)
		-- Our length can go below the length of the array we're shadowing, so handle that case
		if k > #t then
			return nil
		end
		return rawget(t, "__shadow")[k]
	end,
	__newindex = function(t, k, v)
		if k == #t + 1 then
			t.__length = t.__length + 1
		end
		rawset(t, k, v)
	end,
	__len = function(t)
		return t.__length
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
-- We do not attempt to make pairs iterate over all the shadowed elements because this is extremely nontrivial.
local shadowtable_mt = {
	__index = function(t, k)
		return rawget(t, "__shadow")[k]
	end,
}

---@generic T : table
---@param t T
---@return T
function M.shadowtable(t)
	rawset(t, "__lock", true)
	return setmetatable({ __shadow = t, __depth = rawget(t, "__depth") or 1 }, shadowtable_mt)
end

---@generic T
---@param t T[] | { [integer]: T, __length: integer }
---@return { [integer]: T, __length: integer }
function M.shadowarray(t)
	rawset(t, "__lock", true)
	return setmetatable({ __shadow = t, __length = #t, __depth = rawget(t, "__depth") or 1 }, shadowarray_mt)
end

function M.getshadowdepth(t)
	return rawget(t, "__depth") or 0
end

---Given a shadowed table, flattens its values on to the shadowed table below and returns it
---@generic T : table
---@param t T
---@return T
function M.commit(t)
	setmetatable(t, nil)
	local original = t.__shadow
	local length = t.__length
	t.__shadow = nil
	t.__length = nil

	if original then
		rawset(original, "__lock", nil)
	end

	for k, v in pairs(t) do
		rawset(original, k, v)
	end

	-- If this is an array, truncate the shadowed array in case we removed elements
	if length then
		for i = length + 1, #original do
			rawset(original, i, nil)
		end

		if original.__length then
			original.__length = length
		end
	end

	return original
end

---Given a shadowed table, unlocks the shadowed table below (you should drop this table immediately)
---@generic T : table
---@param t T
---@return T
function M.revert(t)
	setmetatable(t, nil)
	local original = t.__shadow
	local length = t.__length
	t.__shadow = nil
	t.__length = nil

	if original then
		rawset(original, "__lock", nil)
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

---@param t table
---@return string
function M.dumptable(t, spaces)
	spaces = spaces or 0
	local s = tostring(t) .. ": "
	for k, v in pairs(t) do
		s = s .. "\n" .. string.rep(" ", spaces)

		if k == "__shadow" then
			s = s .. "  " .. tostring(k) .. ": " .. tostring(M.dumptable(v, spaces + 2))
		else
			s = s .. "  " .. tostring(k) .. ": " .. tostring(v)
		end
	end

	return s
end

local memo_mt = { __mode = "k" }
local memo_end_tag = {}

---cache a function's outputs to ensure purity with respect to identity
---@param fn function
---@return function
function M.memoize(fn)
	local memotab = setmetatable({}, memo_mt)
	local function wrapfn(...)
		local args = { ... }
		local nargs = select("#", ...)
		local thismemo = memotab
		for i = 1, nargs do
			local nextmemo = thismemo[args[i]]
			if not nextmemo then
				nextmemo = setmetatable({}, memo_mt)
				thismemo[args[i]] = nextmemo
			end
			thismemo = nextmemo
		end
		if not thismemo[memo_end_tag] then
			thismemo[memo_end_tag] = fn(...)
		end
		return thismemo[memo_end_tag]
	end
	return wrapfn
end

---strips ansi character attributes (e.g. colors) from a string
---@param s string
---@return string
---@return integer
function M.strip_ansi(s)
	return s:gsub("\x1b[^m]*m", "")
end

function M.here()
	local info = debug.getinfo(2, "Sl")
	return " @ " .. info.source .. ":" .. info.currentline
end

return M
