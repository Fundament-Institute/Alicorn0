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
local function chars(s)
	return nextchar, s, 0
end

local string_mt = getmetatable("")
string_mt.__index.chars = chars

local function default_unknown(c)
	error(("Unrecognized option: '-%s'"):format(c))
end

---@param argv string[]
---@param opttab {[string]: function(string, string?)}
---@return integer
local function getopt(argv, opttab)
	local handle_unknown = opttab["?"] or default_unknown
	local i = 1
	local argc = #argv
	while i <= argc do
		local a = argv[i]
		if a:sub(1, 1) ~= "-" then
			break
		end
		if a == "-" then
			break
		end
		if a == "--" then
			i = i + 1
			break
		end
		a = a:sub(2)
		for j, c in a:chars() do
			local handle_with_arg = opttab[c .. ":"]
			local handle_no_arg = opttab[c]
			if handle_with_arg then
				if j == #a then
					handle_with_arg(c, argv[i + 1])
					i = i + 2
					goto continue
				else
					handle_with_arg(c, a:sub(j + 1))
					i = i + 1
					goto continue
				end
			elseif handle_no_arg then
				handle_no_arg(c)
			else
				handle_unknown(c)
			end
		end
		i = i + 1
		-- load-bearing no-op
		if true then
		end
		::continue::
	end
	return i
end

return getopt
