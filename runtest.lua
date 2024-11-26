--local endTime = os.time() + 3
--while os.time() < endTime do end

require "pretty-printer" -- has side-effect of loading global p()

if jit then
	--jit.off()
	jit.opt.start("maxtrace=10000")
	jit.opt.start("maxmcode=4096")
	jit.opt.start("recunroll=5")
	jit.opt.start("loopunroll=60")
end

local startTime = os.clock()
local checkpointTime = startTime
local checkpointTime2 = startTime
local metalanguage = require "metalanguage"
local evaluator = require "evaluator"
local format = require "format-adapter"
local base_env = require "base-env"
local terms = require "terms"
local exprs = require "alicorn-expressions"
local profile = require "profile"
local getopt = require "getopt"

local interpreter_argv, argv
if arg then -- puc-rio lua, luajit
	local n = -1
	while arg[n] do
		n = n - 1
	end
	interpreter_argv = table.move(arg, n + 1, -1, 0, {})
	argv = table.move(arg, 0, #arg, 0, {})
elseif process.argv then -- luvit
	local file_n = getopt(process.argv, { ["?"] = function() end })
	interpreter_argv = table.move(process.argv, 0, file_n - 1, 0, {})
	argv = table.move(process.argv, file_n, #process.argv, 0, {})
else
	print("Missing or unknown arg table! Using stub")
	interpreter_argv = { [0] = "lua" }
	argv = { [0] = "runtest.lua" }
end
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
local print_usage = false
---@param s string
---@return string[]
local function split_commas(s)
	local subs = {}
	-- "[^,]*" doesn't work due to a bug up until lua 5.3.3 that caused an
	-- extra empty match at the end of the input if the pattern accepts an
	-- empty match. luajit inherits this bug.
	-- so instead we append a comma and use it as a terminator, ensuring
	-- the pattern doesn't accept an empty match, but still allowing us to
	-- have an empty capture given consecutive commas.
	s = s .. ","
	for sub in s:gmatch("(.-),") do
		table.insert(subs, sub)
	end
	return subs
end
local opttab = {
	["S"] = function(_)
		print_src = true
	end,
	["f"] = function(_)
		print_ast = true
	end,
	["s"] = function(_)
		print_inferrable = true
	end,
	["t"] = function(_)
		print_typed = true
	end,
	["v"] = function(_)
		print_evaluated = true
	end,
	["p:"] = function(_, arg)
		if not arg then
			error("-p requires a file argument")
		end
		profile_run = true
		profile_flame = false
		local subargs = split_commas(arg)
		profile_file = subargs[1]
		profile_what = subargs[2] or "match"
	end,
	["P:"] = function(_, arg)
		if not arg then
			error("-P requires a file argument")
		end
		profile_run = true
		profile_flame = true
		local subargs = split_commas(arg)
		profile_file = subargs[1]
		profile_what = subargs[2] or "match"
	end,
	["?"] = function(c)
		print_usage = true
	end,
}
local first_operand = getopt(argv, opttab)

if print_usage then
	print(("Usage: %s [-Sfstv] [-p file[,what] | -P file[,what]]"):format(argv[0]))
	os.exit()
end

print("Interpreter:", table.concat(interpreter_argv, " ", 0))
print("File:", argv[0])
print("Options:", table.concat(argv, " ", 1, first_operand - 1))
print("Operands:", table.concat(argv, " ", first_operand))
if profile_run then
	print("Profile flame?", profile_flame)
	print("Profile file:", profile_file)
	print("Profile what:", profile_what)
end

local prelude = "testfile.alc"

local env = base_env.create()

local shadowed, env = env:enter_block(terms.block_purity.effectful)

local function load_alc_file(name, env)
	local src_file, err = io.open(name)
	if not src_file then
		error(err)
	end
	local src = src_file:read("a")

	checkpointTime = os.clock()
	print("Read code")
	checkpointTime2 = checkpointTime
	if print_src then
		print(src)
	end

	print("Parsing code")
	local code = format.read(src, name)

	checkpointTime = os.clock()
	print(("Parsed! in %.3f seconds"):format(checkpointTime - checkpointTime2))
	checkpointTime2 = checkpointTime
	if print_ast then
		print("Printing raw AST")
		print(format.lispy_print(code))
		print("End printing raw AST")
	end

	print("Expression -> terms")
	if profile_run and profile_what == "match" then
		profile.start()
	end
	local ok, expr, env = code:match({
		exprs.top_level_block(
			metalanguage.accept_handler,
			{ exprargs = exprs.ExpressionArgs.new(terms.expression_goal.infer, env), name = name }
		),
	}, metalanguage.failure_handler, nil)
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
	return expr, env
end

local expr, env = load_alc_file(prelude, env)
if not expr or not env then
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

local gen = require "terms-generators"
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
