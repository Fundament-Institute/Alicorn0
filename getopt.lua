-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local _ = require "lua-ext" -- has side-effect of loading string.chars

---@alias getopt.opt fun(opt_repr: string, keyed_opt_value?: string)

---@type getopt.opt
local function default_opt_unknown(opt_repr)
	error(("Unrecognized option: %q"):format(opt_repr))
end

---@param get_arg_value (fun(): (arg_value: string))
---@param opt_repr string
---@param opt_unknown getopt.opt
---@param unkeyed_opt getopt.opt?
---@param keyed_opt getopt.opt?
local function handle_opt(get_arg_value, opt_repr, opt_unknown, unkeyed_opt, keyed_opt)
	if keyed_opt then
		local handle_with_value = keyed_opt
		handle_with_value(opt_repr, get_arg_value())
	elseif unkeyed_opt then
		local handle_without_value = unkeyed_opt
		handle_without_value(opt_repr)
	else
		local handle_unknown = opt_unknown
		handle_unknown(opt_repr)
	end
end

---@param argv string[]
---@param short_opts {[string]: getopt.opt}
---@param long_opts {[string]: string|getopt.opt}
---@return integer argv_index
local function getopt(argv, short_opts, long_opts)
	local opt_unknown = short_opts["?"] or default_opt_unknown
	local argv_index = 1
	local argc = #argv
	while argv_index <= argc do
		local arg = argv[argv_index]
		if arg:sub(1, 1) ~= "-" then
			break
		end
		if arg == "-" then
			break
		end
		if arg == "--" then
			argv_index = argv_index + 1
			break
		end
		if arg:sub(1, 2) == "--" then
			local arg_equals = arg:find("=", 1, true)
			local opt_repr = arg
			if arg_equals then
				opt_repr = opt_repr:sub(1, arg_equals - 1)
			end
			local opt_repr_substr = opt_repr:sub(3)
			local long_unkeyed_opt = long_opts[opt_repr_substr]
			local long_keyed_opt = long_opts[opt_repr_substr .. ":"]
			if type(long_keyed_opt) == "string" then
				long_keyed_opt = short_opts[long_keyed_opt]
			end
			if type(long_unkeyed_opt) == "string" then
				if long_keyed_opt == nil then
					long_keyed_opt = short_opts[long_unkeyed_opt .. ":"]
				end
				long_unkeyed_opt = short_opts[long_unkeyed_opt]
			end
			local function get_arg_value()
				if arg_equals then
					return arg:sub(arg_equals + 1)
				end
				local next_argv_index = argv_index + 1
				if next_argv_index <= argc then
					local arg_value = argv[next_argv_index]
					argv_index = next_argv_index
					return arg_value
				end
				error(("Value not provided for option: %q"):format(opt_repr))
			end
			handle_opt(get_arg_value, opt_repr, opt_unknown, long_unkeyed_opt, long_keyed_opt)
		else
			local new_arg_wanted = false
			for arg_index, arg_char in arg:chars(2) do
				---@cast arg_index integer
				---@cast arg_char string
				local opt_repr = "-" .. arg_char
				local function get_arg_value()
					local next_argv_index = argv_index + 1
					if arg_index == #arg and next_argv_index <= argc then
						local arg_value = argv[next_argv_index]
						new_arg_wanted, argv_index = true, next_argv_index
						return arg_value
					end
					error(("Value not provided for option: %q"):format(opt_repr))
				end
				---@cast arg_index integer
				---@cast arg_char string
				handle_opt(get_arg_value, opt_repr, opt_unknown, short_opts[arg_char], short_opts[arg_char .. ":"])
				if new_arg_wanted then
					break
				end
			end
		end
		argv_index = argv_index + 1
	end
	return argv_index
end

return getopt
