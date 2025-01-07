-- use the line number information of tokens to format
-- put tokens on a new line if their line number is greater than the current line
-- this is not  a format tool it's a lisp-ifier for the format

local indentation_char = "\t"

---@param ast FormatList
---@param prev_line integer
---@param indentation integer
---@return string
---@return integer
local function unformat_list(ast, prev_line, indentation)
	local acc = ""

	while ast.start_anchor.line > prev_line do
		acc = acc .. "\n" .. string.rep(indentation_char, indentation)
		prev_line = prev_line + 1
	end

	if ast.kind == "list" then
		acc = acc .. "("
		for i, v in ipairs(ast.elements) do
			local res
			res, prev_line = unformat_list(v, prev_line, indentation + 1)
			acc = acc .. res
			if not (i == #ast.elements) then
				acc = acc .. " "
			end
		end

		if string.sub(acc, #acc, #acc) == "\n" then
			acc = acc .. string.rep("\t", indentation)
		end
		acc = acc .. ")"
	elseif ast.kind == "literal" then
		acc = acc .. tostring(ast.val)
	elseif ast.kind == "symbol" then
		acc = acc .. ast.str
	elseif ast.kind == "comment" then
		indentation = indentation + 1
		local multiline_comment = not (ast.start_anchor.line == ast.end_anchor.line)

		if multiline_comment then
			acc = acc .. "####"
		else
			acc = acc .. "#"
		end

		for c in ast.val:gmatch "." do
			if c == "\n" and multiline_comment then
				acc = acc .. c .. string.rep(indentation_char, indentation)
			else
				acc = acc .. c
			end
		end

		acc = acc .. "\n"

		prev_line = ast.end_anchor.line
	elseif ast.kind == "string" then
		indentation = indentation + 1

		local escapes = {
			[ [[\]] ] = [[\\]],
			[ [["]] ] = [[\"]],
			["\n"] = [[\n]],
			["\r"] = [[\r]],
			["\t"] = [[\t]],
		}

		local multiline_string = not (ast.start_anchor.line == ast.end_anchor.line)

		if multiline_string then
			acc = acc .. [[""""]]
		else
			acc = acc .. [["]]
		end
		for _, v in ipairs(ast.elements) do
			for _, c in ipairs(v.val) do
				if (string.char(c) == "\n") and multiline_string then
					acc = acc .. string.char(c) .. string.rep(indentation_char, indentation)
				elseif (not multiline_string) and escapes[string.char(c)] then
					acc = acc .. escapes[string.char(c)]
				else
					acc = acc .. string.char(c)
				end
			end
		end

		if multiline_string then
			acc = acc .. "\n"
		else
			acc = acc .. [["]]
		end

		prev_line = ast.end_anchor.line
	end

	return acc, prev_line
end

---@param ast FormatList
---@return string
local function unformat(ast)
	local acc = ""

	for _, v in ipairs(ast.elements) do
		acc = acc .. "\n" .. unformat_list(v, v.start_anchor.line, 0) .. ""
	end

	return acc
end

return {
	unformat = unformat,
}
