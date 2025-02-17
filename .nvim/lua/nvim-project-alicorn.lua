-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local M = {}

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
	end
end

return M
