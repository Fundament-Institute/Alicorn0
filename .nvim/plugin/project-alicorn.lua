-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

if vim.g.loaded_project_alicorn ~= nil then
	return
end
vim.g.loaded_project_alicorn = true

local project_alicorn_augroup = vim.api.nvim_create_augroup("project.alicorn", {})

local project_path_alicorn = vim.g.project_path_alicorn
if project_path_alicorn ~= nil then
	local escaped_project_path_alicorn = string.gsub(project_path_alicorn, "([*?\\,{}%[%]])", "\\%1")
	local project_alicorn_pattern = escaped_project_path_alicorn .. "/*"
	vim.api.nvim_create_autocmd({ "BufReadPost" }, {
		group = project_alicorn_augroup,
		pattern = project_alicorn_pattern,
		desc = "require('nvim-project-alicorn').on_buf_read(event_args)",
		callback = function(event_args)
			return require("nvim-project-alicorn").on_buf_read(event_args)
		end,
	})
end
