--local endTime = os.time() + 3
--while os.time() < endTime do end

local startTime = os.clock()
local checkpointTime = startTime
local checkpointTime2 = startTime
local metalanguage = require "./metalanguage"
local evaluator = require "./evaluator"
local format = require "./format-adapter"
local base_env = require "./base-env"
local p = require "pretty-print".prettyPrint
local terms = require "./terms"
local exprs = require "./alicorn-expressions"
local profile = require "./profile"
local fs = require "fs"
local path = require "path"

local argv = process.argv
local opts = argv[2]
local print_src = false
local print_ast = false
local print_inferrable = false
local print_typed = false
local print_evaluated = false
local profile_run = false
local profile_flame = false
local profile_file = ""
-- "match", "infer" are currently implemented
local profile_what = ""
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
	if string.find(opts, "e") then
		print_evaluated = true
	end
	if string.find(opts, "p") then
		profile_run = true
		profile_flame = false
		profile_file = argv[3]
		profile_what = argv[4] or "match"
	end
	if string.find(opts, "P") then
		profile_run = true
		profile_flame = true
		profile_file = argv[3]
		profile_what = argv[4] or "match"
	end
end

local filename = path.resolve("testfile.alc")
local src = fs.readFileSync(filename)

checkpointTime = os.clock()
print("Read code")
checkpointTime2 = checkpointTime
if print_src then
	print(src)
end

print("Parsing code")
local code = format.read(src, filename)

checkpointTime = os.clock()
print(("Parsed! in %.3f seconds"):format(checkpointTime - checkpointTime2))
checkpointTime2 = checkpointTime
if print_ast then
	print("Printing raw AST")
	print(format.lispy_print(code))
	print("End printing raw AST")
end

local env = base_env.create()

local shadowed, env = env:enter_block(terms.block_purity.effectful)

print("Expression -> terms")
if profile_run and profile_what == "match" then
	profile.start()
end
local ok, expr, env = code:match(
	{ exprs.block(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, env)) },
	metalanguage.failure_handler,
	nil
)
if profile_run and profile_what == "match" then
	profile.stop()
	if profile_flame then
		profile.dump_flame(profile_file)
	else
		profile.dump(profile_file)
	end
end
if not ok then
	checkpointTime = os.clock()
	print(("Evaluating failed in %.3f seconds"):format(checkpointTime - checkpointTime2))
	print(expr)
	return
end

local env, bound_expr, purity = env:exit_block(expr, shadowed)

checkpointTime = os.clock()
print(("Got a term! in %.3f seconds"):format(checkpointTime - checkpointTime2))
checkpointTime2 = checkpointTime
if print_inferrable then
	print("bound_expr: (inferrable term follows)")
	print(bound_expr:pretty_print(terms.typechecking_context()))
end

print("Inferring")
if profile_run and profile_what == "infer" then
	profile.start()
end
local type, usages, term = evaluator.infer(bound_expr, terms.typechecking_context())
if profile_run and profile_what == "infer" then
	profile.stop()
	if profile_flame then
		profile.dump_flame(profile_file)
	else
		profile.dump(profile_file)
	end
end

checkpointTime = os.clock()
print(("Inferred! in %.3f seconds"):format(checkpointTime - checkpointTime2))
checkpointTime2 = checkpointTime
if print_typed then
	print("type: (value term follows)")
	print(type)
	print("usages:", usages)
	print("term: (typed term follows)")
	print(term:pretty_print(terms.runtime_context()))
end

local gen = require "./terms-generators"
local set = gen.declare_set
local unique_id = gen.builtin_table
evaluator.typechecker_state:flow(
	type,
	nil,
	terms.value.program_type(
		terms.value.effect_row(set(unique_id)(terms.TCState), terms.value.effect_empty),
		evaluator.typechecker_state:metavariable(terms.typechecking_context()):as_value()
	),
	nil,
	"final flow check"
)

print("Evaluating")
local result = evaluator.evaluate(term, terms.runtime_context())

checkpointTime = os.clock()
print(("Evaluated! in %.3f seconds"):format(checkpointTime - checkpointTime2))
checkpointTime2 = checkpointTime
if print_evaluated then
	print("result: (value term follows)")
	print(result)
end

print("Executing")
local result_exec = evaluator.execute_program(result)

checkpointTime = os.clock()
print(("Executed! in %.3f seconds"):format(checkpointTime - checkpointTime2))
checkpointTime2 = checkpointTime
print("result_exec: (value term follows)")
print(result_exec)

print(("Runtest succeeded in %.3f seconds"):format(checkpointTime - startTime))
