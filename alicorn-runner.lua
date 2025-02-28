require("lua-init")

local metalanguage = require "metalanguage"
local evaluator = require "evaluator"
local format = require "format-adapter"
local formatter = require "format"
local base_env = require "base-env"
local terms = require "terms"
local exprs = require "alicorn-expressions"
local profile = require "profile"
local U = require "alicorn-utils"

---@class alicorn.Runner
---@overload fun(class: alicorn.RunnerClass): (self: alicorn.Runner) class method: constructor
---@field env Environment
---@field shadows ShadowEnvironment[]
---@field unparsed_syntax? ConstructedSyntax
local Runner = {}
do
	---@class alicorn.RunnerClass: metatable
	---@overload fun(class: alicorn.RunnerClass): (self: alicorn.Runner) constructor
	local R = Runner --[[@as table]]
	---@param class alicorn.RunnerClass
	---@return alicorn.Runner self
	function R.__call(class)
		---@diagnostic disable-next-line: return-type-mismatch
		return setmetatable({
			env = base_env.create(),
			shadows = {},
			unparsed_syntax = {},
		}, class)
	end
	R.__index = R
	---@diagnostic disable-next-line: param-type-mismatch
	setmetatable(R, R)
end

---@param purity block_purity
---@overload fun(purity: "effectful")
---@overload fun(purity: "pure")
---@overload fun(purity: "dependent", val: flex_value)
---@overload fun(purity: "inherit")
---@diagnostic disable-next-line: incomplete-signature-doc
function Runner:enter_block(purity, ...)
	if type(purity) == "string" then
		local block_purity_constructor = terms.block_purity[purity]
		if block_purity_constructor == nil then
			error(("`Runner:enter_block()`: `terms.block_purity.%s` is nil"):format(tostring(purity)))
		end
		if select('#', ...) > 0 then
			purity = block_purity_constructor(...) --[[@as block_purity]]
		else
			purity = block_purity_constructor --[[@as block_purity]]
		end
	end
	local shadow
	shadow, self.env = self.env:enter_block(purity)
	table.insert(self.shadows, shadow)
end

---@param expr anchored_inferrable
---@return anchored_inferrable expr
---@return purity purity
function Runner:exit_block(expr)
	local shadow = table.remove(self.shadows)
	if shadow == nil then
		error("`Runner:exit_block()`: stack of ShadowEnvironments is empty")
	end
	local purity
	self.env, expr, purity = self.env:exit_block(expr, shadow)
	return expr, purity
end

---@param format_text string
---@param id string
---@return ConstructedSyntax syntax
function Runner:read_format(format_text, id)
	if format_text == nil then
		error("`Runner:read_format()`: `format_text` is nil")
	end
	if id == nil then
		error("`Runner:read_format()`: `id` is nil")
	end
	local syntax = format.read(format_text, id)
	return syntax
end

---@param format_file (string | file*) will call `format_file:read("*a")` if present
---@param id? string when `nil`, `format_file`
---@return ConstructedSyntax syntax
function Runner:read_file(format_file, id)
	if format_file == nil then
		error("`Runner:read_file()`: `format_file` is nil")
	end
	local read, close_file = format_file.read, false
	if read == nil then
		---@cast format_file string
		if id == nil then
			id = format_file
		end
		local file, err = io.open(format_file)
		if file == nil then
			---@cast err -nil
			error(("`Runner:read_file()`: error reading %q: %s"):format(format_file, err))
		end
		format_file, read, close_file = file, file.read, true
	end
	---@cast format_file file*
	local format_text = read(format_file, "*a") --[[@as string]]
	if id == nil then
		error("`Runner:read_file()`: `id` is nil")
	end
	local syntax = self:read_format(format_text, id)
	if close_file then
		format_file:close()
	end
	return syntax
end

---@param syntax ConstructedSyntax
---@param id string
---@return boolean ok
---@return (string | anchored_inferrable) expr
function Runner:try_parse_syntax(syntax, id, ...)
	if select('#', ...) > 0 then
		self:enter_block(...)
	end
	---@type boolean, (string | anchored_inferrable), Environment?
	local ok, expr, env = syntax:match({
		exprs.top_level_block(
			metalanguage.accept_handler,
			{ exprargs = exprs.ExpressionArgs.new(terms.expression_goal.infer, self.env), name = id }
		),
	}, metalanguage.failure_handler, nil)
	if not ok then
		---@cast expr string
		return ok, expr
	end
	---@cast expr anchored_inferrable
	---@cast env Environment
	self.env = env
	if select('#', ...) > 0 then
		local _purity
		expr, _purity = self:exit_block(expr)
	end
	return ok, expr
end

---@param syntax ConstructedSyntax
---@param id string
---@return anchored_inferrable expr
function Runner:parse_syntax(syntax, id, ...)
	local ok, expr = self:try_parse_syntax(syntax, id, ...)
	if not ok then
		---@cast expr string
		error(("`Runner:parse_syntax()`: parsing failed: %s"):format(tostring(expr)))
	end
	---@cast expr -string
	return expr
end

---@param format_text string
---@param id string
---@return boolean ok
---@return (string | anchored_inferrable) expr
function Runner:try_parse_format(format_text, id, ...)
	local syntax = self:read_format(format_text, id)
	local ok, expr = self:try_parse_syntax(syntax, id, ...)
	return ok, expr
end

---@param format_text string
---@param id string
---@return anchored_inferrable expr
function Runner:parse_format(format_text, id, ...)
	local syntax = self:read_format(format_text, id)
	local expr = self:parse_syntax(syntax, id, ...)
	return expr
end

---@param format_file (string | file*)
---@param id string?
---@return boolean ok
---@return (string | anchored_inferrable) expr
function Runner:try_parse_file(format_file, id, ...)
	local syntax
	syntax, id = self:read_file(format_file, id), format_file --[[@as string]]
	local ok, expr = self:try_parse_syntax(syntax, id, ...)
	return ok, expr
end

---@param format_file (string | file*)
---@param id string?
---@return anchored_inferrable expr
function Runner:parse_file(format_file, id, ...)
	local syntax
	syntax, id = self:read_file(format_file, id), format_file --[[@as string]]
	local expr = self:parse_syntax(syntax, id, ...)
	return expr
end

---@param expr anchored_inferrable
---@return boolean ok
---@return (string | flex_value) type
---@return ArrayValue<integer>? usages
---@return typed? term
function Runner:try_infer_expr(expr)
	local ok, type, usages, term = evaluator.infer(expr, self.env.typechecking_context)
	return ok, type, usages, term
end

---@param expr anchored_inferrable
---@return flex_value type
---@return ArrayValue<integer> usages
---@return typed term
function Runner:infer_expr(expr)
	local ok, type, usages, term = self:try_infer_expr(expr)
	if not ok then
		---@cast type string
		error(("`Runner:infer_expr()`: inferrence failed: %s"):format(tostring(type)))
	end
	---@cast type -string
	---@cast usages -nil
	---@cast term -nil
	return type, usages, term
end

---@param type flex_value
---@return boolean ok
---@return string? err
function Runner:try_typecheck_program_type(type)
	local typechecking_context = self.env.typechecking_context
	local ok, err = evaluator.typechecker_state:flow(
		type,
		typechecking_context,
		terms.flex_value.program_type(
			terms.flex_value.effect_row(terms.unique_id_set(terms.TCState, terms.lua_prog)),
			evaluator.typechecker_state:metavariable(typechecking_context):as_flex()
		),
		typechecking_context,
		terms.constraintcause.primitive("final flow check", formatter.anchor_here())
	)
	return ok, err
end

---@param type flex_value
function Runner:typecheck_program_type(type)
	local ok, err = self:try_typecheck_program_type(type)
	if not ok then
		---@cast err string
		error(("`Runner:typecheck_program_type()`: final flow check failed: %s"):format(err))
	end
end

---@param term typed
---@return boolean ok
---@return (string | flex_value) value
function Runner:try_evaluate_term(term)
	local ok, value = pcall(evaluator.evaluate, term, self.env.typechecking_context.runtime_context, self.env.typechecking_context)
	return ok, value
end

---@param term typed
---@return flex_value value
function Runner:evaluate_term(term)
	local value = evaluator.evaluate(term, self.env.typechecking_context.runtime_context, self.env.typechecking_context)
	return value
end

---@param program_expr anchored_inferrable
---@return boolean ok
---@return (string | flex_value) value
function Runner:try_evaluate_program_expr(program_expr)
	local ok, program_type, _program_usages, program_term = self:try_infer_expr(program_expr)
	if not ok then
		---@cast program_type string
		return ok, program_type
	end
	---@cast program_type -string
	---@cast _program_usages -nil
	---@cast program_term -nil
	local err
	ok, err = self:try_typecheck_program_type(program_type)
	if not ok then
		---@cast err string
		return ok, err
	end
	local program_value
	ok, program_value = self:try_evaluate_term(program_term)
	return ok, program_value
end

---@param program_expr anchored_inferrable
---@return flex_value program_value
function Runner:evaluate_program_expr(program_expr)
	local program_type, _program_usages, program_term = self:infer_expr(program_expr)
	self:typecheck_program_type(program_type)
	local program_value = self:evaluate_term(program_term)
	return program_value
end

---@param program_format_text string
---@param program_id string
---@return flex_value program_value
function Runner:evaluate_program_format(program_format_text, program_id, ...)
	local program_expr = self:parse_format(program_format_text, program_id, ...)
	local program_value = self:evaluate_program_expr(program_expr)
	return program_value
end

---@param program_format_file (string | file*)
---@param program_id string?
---@return flex_value program_value
function Runner:evaluate_program_file(program_format_file, program_id, ...)
	local program_expr = self:parse_file(program_format_file, program_id, ...)
	local program_value = self:evaluate_program_expr(program_expr)
	return program_value
end

---@param program_value flex_value
---@return any ...
function Runner:execute_program_value(program_value)
	local program_exec_value = evaluator.execute_program(program_value)
	return program_exec_value:unwrap_host_tuple_value():unpack()
end

---@param program_format_text string
---@param program_id string
---@return any ...
function Runner:execute_program_format(program_format_text, program_id)
	local program_value = self:evaluate_program_format(program_format_text, program_id, terms.block_purity.effectful)
	return self:execute_program_value(program_value)
end

---@param program_format_file (string | file*)
---@param program_id string?
---@return any ...
function Runner:execute_program_file(program_format_file, program_id)
	local program_value = self:evaluate_program_file(program_format_file, program_id, terms.block_purity.effectful)
	return self:execute_program_value(program_value)
end

return { Runner = Runner }
