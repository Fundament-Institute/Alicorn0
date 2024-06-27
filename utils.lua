local M = {}

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

---Exists only to prevent tail call optimizations
---@param ... any
---@return ...
function M.notail(...)
	return ...
end

--- name and info aren't used here because they're inspected by the stacktrace using the debug API if an error occurs
---@param name string
---@param info any
---@param fn fun(...) : ...
---@param ... any
---@return ...
function M.tag(name, info, fn, ...)
	return M.notail(fn(...))
end

return M
