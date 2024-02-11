local metalanguage = require "./metalanguage"
local evaluator = require "./evaluator"
local format = require "./format-adapter"
local base_env = require "./base-env"
local p = require "pretty-print".prettyPrint
local terms = require "./terms"
local exprs = require "./alicorn-expressions"
local fs = require "fs"
local path = require "path"

local filename = path.resolve("testfile.alc")
local src = fs.readFileSync(filename)
print("read code")
print(src)
print("parsing code")
local code = format.read(src, filename)
-- p(code)

local env = base_env.create()

local shadowed, env = env:enter_block()

print("Expression -> terms")
local ok, expr, env = code:match(
	{ exprs.block(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, env)) },
	metalanguage.failure_handler,
	nil
)
if not ok then
	print("evaluating failed")
	print(expr)
	return
end

local env, bound_expr = env:exit_block(expr, shadowed)

print("Inferring")
local type, usages, term = evaluator.infer(bound_expr, terms.typechecking_context())
print("Inferred!")
print("type: (value term follows)")
print(type)
print("usages:", usages)
print("term: (typed term follows)")
print(term)

print("Evaluating")
local result = evaluator.evaluate(term, terms.runtime_context())
print("result: (value term follows)")
print(result)
