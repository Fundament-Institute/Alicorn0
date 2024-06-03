local metalanguage = require "./metalanguage"
local evaluator = require "./evaluator"
local format = require "./format-adapter"
local base_env = require "./base-env"
local p = require "pretty-print".prettyPrint
local terms = require "./terms"
local exprs = require "./alicorn-expressions"
local fs = require "fs"
local path = require "path"

local opts = process.argv[2]
local print_src = false
local print_ast = false
local print_inferrable = false
local print_typed = false
local profile_run = false
local profile_file = ""
if opts then
	if string.find(opts, "S") then
		print_src = true
	end
	if string.find(opts, "A") then
		print_ast = true
	end
	if string.find(opts, "i") then
		print_inferrable = true
	end
	if string.find(opts, "t") then
		print_typed = true
	end
	if string.find(opts, "p") then
		profile_run = true
		profile_file = process.argv[3]
	end
end

local filename = path.resolve("testfile.alc")
local src = fs.readFileSync(filename)
print("read code")

if print_src then
	print(src)
end

print("parsing code")
local code = format.read(src, filename)

if print_ast then
	print("printing raw ast")
	print(format.lispy_print(code))
	print("end printing raw ast")
end

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

print("got a term!")
if print_inferrable then
	print("bound_expr: (inferrable term follows)")
	print(bound_expr:pretty_print(terms.typechecking_context()))
end

print("Inferring")
local profiler = nil
if profile_run then
	profiler = require("jit.p")
	profiler.start("G", profile_file)
end
local type, usages, term = evaluator.infer(bound_expr, terms.typechecking_context())
if profile_run then
	profiler.stop()
end
print("Inferred!")
if print_typed then
	print("type: (value term follows)")
	print(type)
	print("usages:", usages)
	print("term: (typed term follows)")
	print(term:pretty_print(terms.runtime_context()))
end

print("Evaluating")
local result = evaluator.evaluate(term, terms.runtime_context())
print("result: (value term follows)")
print(result)
