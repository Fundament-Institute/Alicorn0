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
---@return integer argv_index
local function getopt(argv, short_opts)
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
		local new_arg_wanted = false
		for arg_index, arg_char in arg:chars(2) do
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
		argv_index = argv_index + 1
	end
	return argv_index
end

return getopt
