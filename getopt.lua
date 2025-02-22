-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local _ = require "lua-ext" -- has side-effect of loading string.chars

local function default_unknown(c)
	error(("Unrecognized option: '-%s'"):format(c))
end

---@param argv string[]
---@param opttab {[string]: fun(string, string?)}
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
					error(("Value not provided for option: '-%s'"):format(c))
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
