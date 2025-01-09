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
---@generic T1, T2, T3, T4, T5, T6, T7, T8
---@param name string
---@param info any
---@param fn fun(...) : T1?, T2?, T3?, T4?, T5?, T6?, T7?, T8?
---@param ... any
---@return T1?, T2?, T3?, T4?, T5?, T6?, T7?, T8?
function M.tag(name, info, fn, ...)
	return M.notail(fn(...))
end

---@param t table
---@param userdata any?
function M.lock_table(t, userdata)
	local mt = getmetatable(t)
	local rawlen = #t

	-- We nest metatables here so that the lock metatable pretends to have all the elements of whatever it's locking.
	setmetatable(
		t,
		setmetatable({
			__newindex = function()
				error("LOCKED TABLE!")
			end,
			__len = function(t)
				return getmetatable(t).__length or rawlen
			end,
			__lock = true,
			-- DEBUG: Comment this out for a significant perf boost if you aren't debugging anything
			__locktrace = debug.traceback("lock created here " .. (userdata or "")),
			__prev = mt,
		}, { __index = mt })
	)
end

---@param t table
function M.unlock_table(t)
	local mt = getmetatable(t)

	if mt and mt.__lock then
		setmetatable(t, mt.__prev)
	else
		error("Tried to unlock a table that was already unlocked! (is this a spurious error???)")
	end
end

---@param t table
---@return boolean
function M.is_locked(t)
	local mt = getmetatable(t)
	return mt and (mt.__lock ~= nil)
end

---@param t table
function M.check_locked(t)
	local mt = getmetatable(t)
	if mt and mt.__lock ~= nil then
		error("Trying to shadow an already shadowed object! This should never happen!" .. (mt.__locktrace or ""))
	end
end

---@param t table
---@return integer
function M.getshadowdepth(t)
	local mt = getmetatable(t)
	if mt == nil or mt.__depth == nil then
		return 0
	end
	return mt.__depth
end

---Insert an element into a list, respecting whether it was a shadowed array or not
---@generic T
---@param list T[]
---@param value T
function M.append(list, value)
	-- If this is a shadowed array it'll trigger the __newindex overload that increments length
	list[#list + 1] = value
end

---Removes an element from a list, respecting whether it was a shadowed array or not
---@generic T
---@param list T[] | { [integer]: T }
---@return T
function M.pop(list)
	M.check_locked(list)

	local value = list[#list]
	rawset(list, #list, nil)
	local mt = getmetatable(list)
	if mt and mt.__length then
		mt.__length = mt.__length - 1
	end
	return value
end

-- This is a metatable that shadows an array
local shadowarray_mt = {
	__index = function(t, k)
		-- Our length can go below the length of the array we're shadowing, so handle that case
		if k > #t then
			return nil
		end
		return getmetatable(t).__shadow[k]
	end,
	__newindex = function(t, k, v)
		if k == #t + 1 then
			getmetatable(t).__length = getmetatable(t).__length + 1
		end
		rawset(t, k, v)
	end,
	__len = function(t)
		return getmetatable(t).__length
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
		return getmetatable(t).__shadow[k]
	end,
}

---@generic T : table
---@param t T
---@param userdata any
---@return T
function M.shadowtable(t, userdata)
	M.check_locked(t)
	M.lock_table(t, userdata)
	return setmetatable({}, { __shadow = t, __depth = M.getshadowdepth(t) + 1, __index = shadowtable_mt.__index })
end

---@generic T
---@param t T[]
---@param userdata any
---@return { [integer]: T}
function M.shadowarray(t, userdata)
	M.check_locked(t)
	M.lock_table(t, userdata)

	return setmetatable({}, {
		__shadow = t,
		__length = #t,
		__depth = M.getshadowdepth(t) + 1,
		__index = shadowarray_mt.__index,
		__newindex = shadowarray_mt.__newindex,
		__len = shadowarray_mt.__len,
		__ipairs = shadowarray_mt.__ipairs,
	})
end

---Given a shadowed table, flattens its values on to the shadowed table below and returns it
---@generic T : table
---@param t T
---@return T
function M.commit(t)
	local mt = getmetatable(t)
	local original = mt.__shadow
	local length = mt.__length
	setmetatable(t, nil)

	if original then
		M.unlock_table(original)
	end

	for k, v in pairs(t) do
		rawset(original, k, v)
	end

	-- If this is an array, truncate the shadowed array in case we removed elements
	if length then
		for i = length + 1, #original do
			rawset(original, i, nil)
		end

		local orig_mt = getmetatable(original)
		if orig_mt and orig_mt.__length then
			orig_mt.__length = length
		end
	end

	M.invalidate(t)
	return original
end

---Given a shadowed table, unlocks the shadowed table below (you should drop this table immediately)
---@generic T : table
---@param t T
---@return T
function M.revert(t)
	local mt = getmetatable(t)
	local original = mt.__shadow
	setmetatable(t, nil)

	if original then
		M.unlock_table(original)
	end

	M.invalidate(t)
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
		s = s .. "\n" .. string.rep(" ", spaces) .. "  " .. tostring(k) .. ": " .. tostring(v)
	end

	local mt = getmetatable(t)
	if mt and mt.__shadow then
		s = s .. "\n" .. string.rep(" ", spaces) .. "  [shadows]: " .. tostring(M.dumptable(mt.__shadow, spaces + 2))
	end

	return s
end

function M.rawdump(t, spaces)
	local mt = getmetatable(t)
	setmetatable(t, nil)
	spaces = spaces or 0
	local s = tostring(t) .. ": " .. tostring(mt)
	for k, v in pairs(t) do
		s = s .. "\n" .. string.rep(" ", spaces)
		s = s .. "  " .. tostring(k) .. ": " .. tostring(v)
	end

	setmetatable(t, mt)
	return s
end

local invalidate_mt = {
	__index = function()
		error("INVALID TABLE")
	end,
	__newindex = function()
		error("INVALID TABLE")
	end,
	__len = function()
		error("INVALID TABLE")
	end,
	__ipairs = function()
		error("INVALID TABLE")
	end,
	__pairs = function()
		error("INVALID TABLE")
	end,
	__call = function()
		error("INVALID TABLE")
	end,
}

---@param t table
function M.invalidate(t)
	setmetatable(t, invalidate_mt)
end

function M.is_invalid(t)
	return getmetatable(t) == invalidate_mt
end

local memo_mt = { __mode = "k" }
local memo_end_tag = {}

---cache a function's outputs to ensure purity with respect to identity
---@param fn function
---@return function
function M.memoize(fn)
	local memotab = setmetatable({}, memo_mt)
	local function wrapfn(...)
		local args = table.pack(...)
		local thismemo = memotab
		for i = 1, args.n do
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

---@param s string
---@return string[]
function M.split_commas(s)
	local subs = {}
	-- "[^,]*" doesn't work due to a bug up until lua 5.3.3 that caused an
	-- extra empty match at the end of the input if the pattern accepts an
	-- empty match. luajit inherits this bug.
	-- so instead we append a comma and use it as a terminator, ensuring
	-- the pattern doesn't accept an empty match, but still allowing us to
	-- have an empty capture given consecutive commas.
	s = s .. ","
	for sub in s:gmatch("(.-),") do
		table.insert(subs, sub)
	end
	return subs
end

---strips ansi character attributes (e.g. colors) from a string
---@param s string
---@return string
---@return integer
function M.strip_ansi(s)
	return s:gsub("\x1b%[[^m]*m", "")
end

function M.here()
	local info = debug.getinfo(2, "Sl")
	return " @ " .. info.source .. ":" .. info.currentline
end

function M.file_is_terminal(input_file)
	-- TODO
	return false
end

-- TODO: check if output is terminal before adding color sequences
---@param s string
---@return string
function M.outputGreen(s)
	return "\27[32m" .. s .. "\27[0m"
end
function M.outputRed(s)
	return "\27[31m" .. s .. "\27[0m"
end

function M.get_cursor_position(input_file, output_file)
	if input_file == nil then
		input_file = io.input()
	end
	if output_file == nil then
		output_file = io.output()
	end
	output_file:write("\x1b[6n")
	local terminal_data = input_file:read(1)
	if terminal_data ~= "\x9b" then
		terminal_data = terminal_data .. input_file:read(1)
		assert(terminal_data == "\x1b[")
	end
	terminal_data = input_file:read("*n")
	assert(terminal_data ~= nil)
	local cursor_line = terminal_data
	terminal_data = input_file:read(1)
	assert(terminal_data == ";")
	terminal_data = input_file:read("*n")
	assert(terminal_data ~= nil)
	local cursor_column = terminal_data
	terminal_data = input_file:read(1)
	assert(terminal_data == "R")
	return cursor_line, cursor_column
end

-- https://gist.github.com/Badgerati/3261142
-- Returns the Levenshtein distance between the two given strings
function M.levenshtein(str1, str2)
	local len1 = string.len(str1)
	local len2 = string.len(str2)
	local matrix = {}
	local cost = 0

	-- quick cut-offs to save time
	if len1 == 0 then
		return len2
	elseif len2 == 0 then
		return len1
	elseif str1 == str2 then
		return 0
	end

	-- initialise the base matrix values
	for i = 0, len1, 1 do
		matrix[i] = {}
		matrix[i][0] = i
	end
	for j = 0, len2, 1 do
		matrix[0][j] = j
	end

	-- actual Levenshtein algorithm
	for i = 1, len1, 1 do
		for j = 1, len2, 1 do
			if str1:byte(i) == str2:byte(j) then
				cost = 0
			else
				cost = 1
			end

			matrix[i][j] = math.min(matrix[i - 1][j] + 1, matrix[i][j - 1] + 1, matrix[i - 1][j - 1] + cost)
		end
	end

	-- return the last value - this is the Levenshtein distance
	return matrix[len1][len2]
end

return M
