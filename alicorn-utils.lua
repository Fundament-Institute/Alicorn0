-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local M = {}

local ipairs, select, setmetatable, table_pack, table_unpack = ipairs, select, setmetatable, table.pack, table.unpack

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

---@module "_meta/alicorn-utils/notail"
function M.notail(...)
	return ...
end

---@generic K, V
---@param tbl table<K, V>
---@return K[]
function M.table_keys(tbl)
	---@type K[]
	local tbl_keys = {}
	local tbl_keys_length = 0
	local key = nil
	while true do
		key = next(tbl, key)
		if key == nil then
			break
		end
		tbl_keys_length = tbl_keys_length + 1
		tbl_keys[tbl_keys_length] = key
	end
	return tbl_keys
end

---@generic T: table, K, V
---@param tbl T
---@param comp? fun(a: K, b: K):boolean
---@return (fun(tbl: table<K, V>, i?: integer): integer, K, V) next
---@return {tbl: T, tbl_keys: K[], tbl_keys_length: integer} state
---@return integer i
function M.table_stable_pairs(tbl, comp)
	local function table_stable_next(state, i)
		if i <= state.tbl_keys_length then
			local key = state.tbl_keys[i]
			return i + 1, key, state.tbl[key]
		end
	end

	local tbl_keys = M.table_keys(tbl)
	table.sort(tbl_keys, comp)
	local state = { tbl = tbl, tbl_keys = tbl_keys, tbl_keys_length = #tbl_keys }
	-- Return an iterator function, the state, starting point
	return table_stable_next, state, 1
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

	if mt == nil then
		mt = {}
		mt.__newindex = function(n, k, v)
			if mt.__lock then
				error("LOCKED TABLE! " .. M.strip_ansi(mt.__locktrace or ""))
			end
			rawset(n, k, v)
		end
		setmetatable(t, mt)
	end

	mt = getmetatable(t)
	if mt.__lock then
		error("Tried to lock a table that was already locked! " .. M.strip_ansi(mt.__locktrace or ""))
	end

	mt.__lock = true
	-- DEBUG: comment this out if you don't need it to make things go faster
	-- mt.__locktrace = debug.traceback("lock created here " .. (userdata or ""))
end

---@param t table
function M.unlock_table(t)
	local mt = getmetatable(t)

	if mt and mt.__lock then
		mt.__lock = false
		mt.__locktrace = nil
	else
		error("Tried to unlock a table that was already unlocked!")
	end
end

---@param t table
---@return boolean
function M.is_locked(t)
	local mt = getmetatable(t)
	return mt and mt.__lock
end

---@param t table
---@param shadow boolean?
function M.check_locked(t, shadow)
	local mt = getmetatable(t)
	if mt and mt.__lock then
		if shadow then
			error(
				"Trying to shadow an already shadowed object! This should never happen!"
					.. M.strip_ansi(mt.__locktrace or "")
			)
		else
			error("Trying to modify a shadowed object! This should never happen!" .. M.strip_ansi(mt.__locktrace or ""))
		end
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
local shadowarray_mt = {}

-- This is a metatable that shadows a dictionary, pretending to have all of it's elements without actually affecting it
-- We do not attempt to make pairs iterate over all the shadowed elements because this is extremely nontrivial.
---@generic T : table
---@param obj T
---@param userdata any
---@return T
function M.shadowtable(obj, userdata)
	M.check_locked(obj, true)
	M.lock_table(obj, userdata)
	local mt = {
		__shadow = obj,
		__depth = M.getshadowdepth(obj) + 1,
	}

	mt.__index = function(t, k)
		return mt.__shadow[k]
	end
	mt.__newindex = function(t, k, v)
		if mt.__lock then
			error("LOCKED TABLE! " .. M.strip_ansi(mt.__locktrace or ""))
		end
		rawset(t, k, v)
	end
	mt.__pairs = function(tbl)
		local keys = {}
		local t = tbl
		local k, _ = next(t, nil)
		while k do
			keys[k] = true
			k, _ = next(t, k)
		end
		t = mt.__shadow
		while t ~= nil do
			local k, _ = next(t, nil)
			while k do
				keys[k] = true
				k, _ = next(t, k)
			end
			t = getmetatable(t)
			if t then
				t = t.__shadow
			end
		end

		local function iter(t, ind)
			local k, v = next(keys, ind)
			if v ~= nil then
				return k, tbl[k]
			end
			return nil
		end

		return iter, tbl, nil
	end

	return M.notail(setmetatable({}, mt))
end

local function rawpairs(tbl)
	local function iter(t, ind)
		local k, v = next(t, ind)
		if v ~= nil then
			return k, v
		end
		return nil
	end
	return iter, tbl, nil
end

---@generic T
---@param obj T[]
---@param userdata any
---@return { [integer]: T}
function M.shadowarray(obj, userdata)
	M.check_locked(obj, true)
	M.lock_table(obj, userdata)

	local mt = {
		__shadow = obj,
		__length = #obj,
		__depth = M.getshadowdepth(obj) + 1,
	}
	mt.__index = function(t, k)
		-- Our length can go below the length of the array we're shadowing, so handle that case
		if k > #t then
			return nil
		end
		return mt.__shadow[k]
	end
	mt.__newindex = function(t, k, v)
		if mt.__lock then
			error("LOCKED TABLE! " .. M.strip_ansi(mt.__locktrace or ""))
		end
		if k == #t + 1 then
			mt.__length = mt.__length + 1
		end
		rawset(t, k, v)
	end
	mt.__len = function(t)
		return mt.__length
	end
	mt.__ipairs = function(tbl)
		return function(t, i)
			i = i + 1
			local v = t[i]
			if nil ~= v then
				return i, v
			end
		end, tbl, 0
	end

	return M.notail(setmetatable({}, mt))
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
	local s = { tostring(t) .. ": " }
	for k, v in pairs(t) do
		s[#s + 1] = string.rep(" ", spaces) .. "  " .. tostring(k) .. ": " .. tostring(v)
	end

	local mt = getmetatable(t)
	if mt and mt.__shadow then
		s[#s + 1] = string.rep(" ", spaces) .. "  [shadows]: " .. tostring(M.dumptable(mt.__shadow, spaces + 2))
	end

	return M.notail(table.concat(s, "\n"))
end

---@param t table
---@return string
function M.dumptree(t, spaces)
	spaces = spaces or 0
	local s = tostring(t) .. ": "
	for k, v in pairs(t) do
		s = s .. "\n" .. string.rep(" ", spaces) .. "  " .. tostring(k) .. ": "
		if type(v) == "table" then
			s = s .. M.dumptable(v, spaces + 2)
		else
			s = s .. tostring(v)
		end
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
local memo_nil_tag = {}

---cache a function's outputs to ensure purity with respect to identity
---@generic F: function
---@param fn F
---@param args_table boolean Whether the function takes a single arguments table
---@return F
function M.memoize(fn, args_table)
	local memotab = setmetatable({}, memo_mt)
	if args_table then
		local function wrapfn(args)
			local thismemo = memotab
			local n = args.n
			if n == nil then
				n = #args
			end
			for i = 1, n do
				this_arg = args[i]
				if this_arg == nil then
					this_arg = memo_nil_tag
				end
				local nextmemo = thismemo[this_arg]
				if not nextmemo then
					nextmemo = setmetatable({}, memo_mt)
					thismemo[this_arg] = nextmemo
				end
				thismemo = nextmemo
			end
			if not thismemo[memo_end_tag] then
				thismemo[memo_end_tag] = table_pack(fn(args))
			end
			local values = thismemo[memo_end_tag]
			return table_unpack(values, 1, values.n)
		end
		return wrapfn
	end
	local function wrapfn(...)
		local thismemo = memotab
		for i = 1, select("#", ...) do
			local this_arg = select(i, ...)
			if this_arg == nil then
				this_arg = memo_nil_tag
			end
			local nextmemo = thismemo[this_arg]
			if not nextmemo then
				nextmemo = setmetatable({}, memo_mt)
				thismemo[this_arg] = nextmemo
			end
			thismemo = nextmemo
		end
		if not thismemo[memo_end_tag] then
			thismemo[memo_end_tag] = table_pack(fn(...))
		end
		local values = thismemo[memo_end_tag]
		return table_unpack(values, 1, values.n)
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

function M.here(offset)
	if debug == nil then
		return "<no debug info>"
	end
	local info = debug.getinfo((offset or 1) + 1, "Sl")
	return info.source .. ":" .. info.currentline
end

function M.bound_here(offset)
	-- DEBUG: Uncomment this if you want to know where a bound variable or closure is
	--local info = debug.getinfo((offset or 1) + 1, "Sl")
	--return info.source .. ":" .. info.currentline
	return ""
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

---This function is made easier because we know we're ALWAYS inserting a new item, so we ALWAYS shadow any tables we
---encounter that aren't shadowed yet (and also aren't new insertions on this layer).
---@generic T, U
---@param obj U
---@param store { [integer]: { [integer]: T } }?
---@param i integer
---@param extractors (fun(obj: U):integer)[]
---@param level integer
---@return { [integer]: T }
function M.insert_tree_node(obj, store, i, extractors, level)
	if store == nil then
		store = {}
		--level = -1
	end

	M.check_locked(store)

	local curlevel = M.getshadowdepth(store)
	if i > #extractors then
		if level > 0 then
			for j = curlevel + 1, level do
				store = M.shadowarray(store)
			end
			if M.getshadowdepth(store) ~= level then
				error("Improper shadowing happened!")
			end
		end
		M.append(store, obj)
		return store
	end
	local kx = extractors[i]
	local key = kx(obj)
	if level > 0 then
		-- shadow the node enough times so that the levels match
		for j = curlevel + 1, level do
			store = M.shadowtable(store)
		end
		if M.getshadowdepth(store) ~= level then
			error("Improper shadowing happened!")
		end
	end
	-- Note: it might be *slightly* more efficient to only reassign if the returned table is different, but the commit
	-- only copies completely new keys anyway so it doesn't really matter.
	store[key] = M.insert_tree_node(obj, store[key], i + 1, extractors, level)

	-- Any time we shadow something more than once, we have some "skipped" levels in-between that must be assigned
	--[[local parent = store
	local child = store[key]
	local newlevel = M.getshadowdepth(child)
	for j = oldlevel + 1, newlevel - 1 do
		parent = getmetatable(parent).__shadow
		child = getmetatable(child).__shadow
		rawset(parent, key, child)
	end
]]
	return store
end

---@generic T
---@param node { [integer]: T }
---@param depth integer
---@return { [integer]: T }
function M.commit_tree_node(node, depth)
	if M.getshadowdepth(node) < depth then
		return node
	end
	local mt = getmetatable(node)
	local base = mt.__shadow
	local isleaf = mt.__length ~= nil
	setmetatable(node, nil)
	M.unlock_table(base)

	if base then
		-- Because we sometimes skip shadow layers, this can sometimes be at the wrong shadow level
		while M.getshadowdepth(base) < (depth - 1) do
			if isleaf then
				base = M.shadowarray(base)
			else
				base = M.shadowtable(base)
			end
		end

		for k, v in rawpairs(node) do
			-- If this is an array, we only copy keys that do not exist at all in the shadowed table
			if (not isleaf) or base[k] == nil then
				rawset(base, k, M.commit_tree_node(v, depth))
			end
		end
		M.invalidate(node)
		return base
	end
	return node
end

---@generic T
---@param node { [integer]: { [integer]: T } }
---@param depth integer
---@return { [integer]: T }
function M.revert_tree_node(node, depth)
	if M.getshadowdepth(node) < depth then
		return node
	end
	local mt = getmetatable(node)
	local base = mt.__shadow
	setmetatable(node, nil)
	if base then
		for k, v in rawpairs(node) do
			M.revert_tree_node(v, depth)
		end
		M.unlock_table(base)
		M.invalidate(node)

		-- If this is a vestigial shadow, revert it too. This is safe because the observed behavior doesn't change, and it is necessary because we "skip" layers of the tree when making shadows.
		local anykey, _ = next(base, nil)
		while anykey == nil and getmetatable(base) and getmetatable(base).__shadow do
			node = base
			base = getmetatable(node).__shadow
			M.unlock_table(base)
			M.invalidate(node)
			anykey, _ = next(base, nil)
		end
		return base
	end
	return node
end

local litprint_mt = {
	__tostring = function(val)
		return val.contents
	end,
}

-- turns a string into a table whose __tostring returns the original string
-- useful for passing a string into tag() to prevent it from being %q formatted
-- by the pretty-printer
---@param s string
---@return table
function M.litprint(s)
	return M.notail(setmetatable({ contents = s }, litprint_mt))
end

function M.debug_break()
	return require("lua-init").debug_break()
end

DEBUG_ID = 0
function M.debug_id()
	DEBUG_ID = DEBUG_ID + 1

	-- Use this to reliably breakpoint at the moment a term of interest is created
	--if DEBUG_ID == 115726 then
	--	M.debug_break()
	--end

	return DEBUG_ID
end

-- this function should be called as an xpcall error handler
---@param err table | string
---@param prefix string?
---@param level integer?
---@return table | string
function M.custom_traceback(err, prefix, level)
	if type(err) == "table" then
		return err
	end
	if prefix == nil then
		prefix = ""
	end
	---@type string[]
	local s =
		{ type(err) == "string" and err or ("must pass string or table to error handler, found: " .. tostring(err)) }
	if level == nil then
		level = 0
	end
	local i = 3 + level
	if debug then
		local info = debug.getinfo(i, "Sfln")
		while info ~= nil do
			if info.func == M.tag then
				local _, name = debug.getlocal(i, 1)
				local _, tag = debug.getlocal(i, 2)
				local _, fn = debug.getlocal(i, 3)
				--i = i + 1
				--info = debug.getinfo(i, "Sfln")
				local ok, err = pcall(function()
					s[#s + 1] = string.format("%s [%s:%d] (%s)", name, info.short_src, info.currentline, pdump(tag))
				end)
				if not ok then
					s[#s + 1] =
						string.format("TRACE FAIL: %s [%s:%d] (%s)", name, info.short_src, info.currentline, err)
				end
			else
				local name = info.name or string.format("<%s:%d>", info.short_src, info.linedefined)
				local args = {}
				local j = 1
				local arg, v = debug.getlocal(i, j)
				while arg ~= nil do
					table.insert(
						args,
						(type(v) == "table") and "<" .. arg .. ":table>" or string.sub(tostring(v), 1, 12)
					)
					j = j + 1
					arg, v = debug.getlocal(i, j)
				end

				--s[#s + 1] = string.format("%s [%s:%d] (%s)", name, info.short_src, info.currentline, table.concat(args,","))
				s[#s + 1] = string.format("%s [%s:%d]", name, info.short_src, info.currentline)
			end
			i = i + 1
			info = debug.getinfo(i, "Sfln")
		end
	end

	return M.notail(table.concat(s, "\n" .. prefix))
end

-- this function should be used when calling for a trace directly
---@param err table | string
---@return table | string
function M.stack_trace(err)
	return M.notail(M.custom_traceback(err))
end

local internals_interface = require "internals-interface"
internals_interface.U = M
return M
