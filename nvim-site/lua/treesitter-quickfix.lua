-- SPDX-License-Identifier: Unlicense
-- SPDX-FileCopyrightText: 2022 Dr. David A. Kunz <david.kunz@sap.com>
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>
-- from <https://github.com/David-Kunz/ts-quickfix>

local M = {}

M.default_opts = {
	capture_filter = function(opts, file, parser, query, id, node, metadata, match)
		local capture_name = query.captures[id]
		return capture_name:find("_", 1, true) ~= 1
	end,
}

---@param file {bufnr?: integer, filename?: string, parser?: vim.treesitter.LanguageTree, str?: string}
local function quickfix_file(opts, qf_table, file)
	local loaded_buffer = false
	local bufnr = file.bufnr
	local parser = file.parser
	if parser == nil and bufnr == nil and file.filename ~= nil then
		if vim.fn.bufexists(file.filename) then
			bufnr = vim.fn.bufadd(file.filename)
			if bufnr > 0 then
				file.bufnr = bufnr
				loaded_buffer = vim.api.nvim_buf_is_loaded(bufnr)
			else
				error(string.format("bufnr for %s is < 0: %s", tostring(file.filename), tostring(bufnr)))
			end
		end
	end
	if parser == nil and loaded_buffer and bufnr ~= nil then
		parser = vim.treesitter.get_parser(bufnr, nil, file.parser_opts)
	end
	if parser == nil and file.str == nil and file.filename ~= nil then
		file.filename = vim.fs.normalize(file.filename)
		if opts.async then
			local file_handle = require("nio.file").open(file.filename, "r")
			file.str = file_handle.read()
			local err = file_handle.close()
			if err ~= nil then
				error(err)
			end
		else
			local file_handle, err = io.open(file.filename, "r")
			if file_handle == nil then
				error(err)
			end
			file.str = file_handle:read("*a")
			file_handle:close()
		end
	end
	if parser == nil and file.str ~= nil and file.lang ~= nil then
		parser = vim.treesitter.get_string_parser(file.str, file.lang, file.parser_opts)
	end
	if parser == nil then
		return
	end
	local query
	if opts.name ~= nil then
		query = vim.treesitter.query.get(parser:lang(), opts.name)
	elseif opts.query_string then
		local ok, q = pcall(vim.treesitter.query.parse, parser:lang(), opts.query_string)
		if ok then
			query = q
		end
	end
	if query == nil then
		return
	end
	local tree = parser:parse()[1]
	for id, node, metadata, match in query:iter_captures(tree:root(), parser:source()) do
		if opts.capture_filter(opts, file, parser, query, id, node, metadata, match) then
			local text = vim.treesitter.get_node_text(node, parser:source())
			local start_row, start_col = node:range()
			table.insert(qf_table, {
				bufnr = bufnr,
				filename = file.filename,
				lnum = start_row + 1,
				col = start_col + 1,
				text = text,
			})
		end
	end
end

function M.quickfix(opts)
	local qf_table = {}
	opts = vim.tbl_extend("force", M.default_opts, opts)
	local files = opts.files
	if files == nil then
		files = { { bufnr = vim.api.nvim_get_current_buf() } }
	end
	local functions = vim.tbl_map(function(file)
		return quickfix_file(opts, qf_table, file)
	end, files)
	if opts.async then
		require("nio").gather(functions)
	else
		for _, func in ipairs(functions) do
			func()
		end
	end
	if next(qf_table) then
		vim.fn.setqflist(qf_table)
		vim.cmd.copen()
	end
end

function M.query_name(name, files, opts)
	M.quickfix(vim.tbl_extend("keep", { name = name, files = files }, opts or {}))
end

function M.query(query_string, files, opts)
	M.quickfix(vim.tbl_extend("keep", { query_string = query_string, files = files }, opts or {}))
end

function M.todo()
	M.query('((comment) @comment (#match? @comment "[^a-zA-Z0-9](TODO|HACK|WARNING|BUG|FIXME|XXX|REVISIT)"))')
end

return M
