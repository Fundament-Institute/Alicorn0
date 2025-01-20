-- string.chars
-- intended usage: for i, c in mystring:chars() do ... end
-- instead of:     for i = 1, #mystring do local c = mystring:sub(i, i) ... end

---@param state string
---@param control integer
---@return integer?
---@return string?
local function nextchar(state, control)
	local i = control + 1
	if i > #state then
		return nil
	else
		return i, state:sub(i, i)
	end
end

---@param s string
---@return function, string, integer
function string.chars(s)
	return nextchar, s, 0
end

-- table.concat
-- in lua 5.2 and below, and luajit, stdlib table.concat ignores the __index
-- metamethod. unlike ipairs, there is no associated metamethod for
-- table.concat, so either we're careful to avoid table.concat on terms-gen
-- arrays (not happening), or we redefine the function.
-- lua 5.3 doesn't need this patch but it also doesn't hurt

---@param list (string|number)[]
---@param sep string?
---@param i integer?
---@param j integer?
---@return string
function table.concat(list, sep, i, j)
	sep = sep or ""
	i = i or 1
	j = j or #list
	if i > j then
		return ""
	end
	local s = list[i]
	for x = i + 1, j do
		s = s .. sep .. list[x]
	end
	return s
end

-- if you're looking for table.pack/unpack, they aren't needed since we're
-- targetting lua 5.3, and luajit with lua 5.2 compat enabled, which already
-- supply them.
-- if you're looking for global unpack, stop using it!
