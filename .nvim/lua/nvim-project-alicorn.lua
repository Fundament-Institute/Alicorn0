-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local M = {}

---@alias nvim-project-alicorn.watched_file<T, U> ({ path: string, handle?: uv_fs_event_t, data: T } | { path: string, err: U })

---@type nvim-project-alicorn.watched_file<table, string>
M.vscode_shared_settings = {}
---@type nvim-project-alicorn.watched_file<table, string>
M.vscode_local_settings = {}

---@generic T
---@param state nvim-project-alicorn.watched_file<T>
---@param on_event fun(state: nvim-project-alicorn.watched_file<T>, err?: string, filename: string, events: uv.aliases.fs_event_start_callback_events)
function M.watch_file(state, on_event)
end

---@param state nvim-project-alicorn.watched_file<table, string>
---@param path string
local function read_json_file(state, path)
	if state.path ~= path then
		state.path = path
	elseif state.data ~= nil then
		return
	end
	local file, err = io.open(path, "r")
	if file == nil then
		---@cast err -nil
		state.data, state.err = nil, err
		return
	end
	local content = file:read("*a")
	if content == nil then
		state.data, state.err = nil, "couldn't read file lines"
		return
	end
	local ok, data = pcall(vim.json.decode, content)
	if not ok then
		---@cast data string
		state.data, state.err = nil, data
	end
	state.data, state.err = data, nil
end

function M.read_vscode_shared_settings()
	local project_path_alicorn = vim.g.project_path_alicorn --[[@as string]]
	local vscode_shared_settings_path = vim.fs.joinpath(project_path_alicorn, ".vscode", "settings.shared.json")
	read_json_file(M.vscode_shared_settings, vscode_shared_settings_path)
end

function M.read_vscode_local_settings()
	local project_path_alicorn = vim.g.project_path_alicorn --[[@as string]]
	local vscode_local_settings_path = vim.fs.joinpath(project_path_alicorn, ".vscode", "settings.local.json")
	read_json_file(M.vscode_local_settings, vscode_local_settings_path)
end

-- do
-- 	local function can_merge(v)
-- 		return type(v) == "table" and (vim.tbl_isempty(v) or not vim.islist(v))
-- 	end
--
-- 	---@param shared table<any, any>
-- 	---@param local table<any, any>
-- 	---@return table<any, any>
-- 	local function array_merge(shared, local)
--  		---@type table<any, any>
-- 		local merged = {}
--   		if vim._empty_dict_mt ~= nil and shared == vim._empty_dict_mt then
--     			merged = vim.empty_dict()
--   		end
-- 		for k, v in pairs(shared) do
-- 			local merged_v = merged[k]
-- 			if can_merge(v) and can_merge(merged_v) then
-- 				merged[k] = array_merge
-- 		end
-- 	end
-- 	M._array_merge = array_merge
-- end

---@return table
function M.get_vscode_settings()
	M.read_vscode_shared_settings()
	M.read_vscode_local_settings()
	---@type table<any, any>
	local vscode_shared_settings = M.vscode_shared_settings.data or {}
	---@type table<any, any>
	local vscode_local_settings = M.vscode_local_settings.data or {}
	local array_merge = vscode_local_settings["workspaceConfigPlus.arrayMerge"] or vscode_shared_settings["workspaceConfigPlus.arrayMerge"]
	if array_merge then
		local islist, list_extend = vim.islist, vim.list_extend
		---@type table<any, any>
		local vscode_settings = {}
		for key, value in pairs(vscode_shared_settings) do
			vscode_settings[key] = value
		end
		for key, value in pairs(vscode_local_settings) do
			local merged_value = vscode_settings[key]
			if islist(merged_value) and islist(value) then
				---@cast value any[]
				---@cast merged_value any[]
				merged_value = list_extend({}, merged_value)
				list_extend(merged_value, value)
			else
				merged_value = value
			end
			vscode_settings[key] = merged_value
		end
		return vscode_settings
	else
		return vim.tbl_extend('force', vscode_shared_settings, vscode_local_settings)
	end
end

function M.get_rust_analyzer_config(vscode_settings)
	if vscode_settings == nil then
		vscode_settings = M.get_vscode_settings()
	end
	local rust_analyzer_config = {}
	for vscode_k, v in pairs(vscode_settings) do
		if vscode_k:find("rust-analyzer.", 1, true) == 1 then
			local config_path = vim.split(vscode_k:sub(15), ".", { plain = true })
			local c = rust_analyzer_config
			local config_path_length = #config_path
			for i, k in ipairs(config_path) do
				if i == config_path_length then
					c[k] = v
					break
				end
				local next_c = c[k]
				if next_c == nil then
					next_c = {}
					c[k] = next_c
				end
				c = next_c
			end
		end
	end
	return rust_analyzer_config
end

function M.on_buf_read(event_args)
	local api = vim.api
	if vim.g.loaded_ale ~= nil then
		local buf_vars = vim.b[event_args.buf]
		ale_fixers = buf_vars.ale_fixers
		if ale_fixers == nil then
			ale_fixers = {}
		end
		ale_fixers = vim.tbl_extend("force", ale_fixers, {
			lua = vim.site.list_extend_unique(ale_fixers.lua or {}, { "stylua" }),
		})
		buf_vars.ale_fixers = ale_fixers

		local vscode_settings = M.get_vscode_settings()
		buf_vars.ale_rust_analyzer_config = M.get_rust_analyzer_config(vscode_settings)
	end
end

return M
