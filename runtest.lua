--local endTime = os.time() + 3
--while os.time() < endTime do end

require "pretty-printer" -- has side-effect of loading global p()

--jit.off()
jit.opt.start("maxtrace=10000")
jit.opt.start("maxmcode=4096")
jit.opt.start("recunroll=5")
jit.opt.start("loopunroll=60")

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
local json = require "libs.dkjson"

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
local test_harness = false
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
	["T"] = function(_)
		test_harness = true
	end,
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
	print(("Usage: %s [-TSfstv] [-p file[,what] | -P file[,what]]"):format(argv[0]))
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

---@enum failurepoint
local failurepoint = {
	parsing = "parsing",
	termgen = "termgen",
	typechecking = "typechecking",
	evaluating = "evaluating",
	executing = "executing",
	success = "success",
}

---@param name string
---@param env Environment
---@param log function
---@return boolean
---@return failurepoint |  inferrable
---@return nil | Environment
local function load_alc_file(name, env, log)
	local src_file, err = io.open(name)
	if not src_file then
		error(err)
	end
	local src = src_file:read("a")

	checkpointTime = os.clock()
	log("Read code")
	checkpointTime2 = checkpointTime
	if print_src then
		log(src)
	end

	log("Parsing code")
	local ok, code = pcall(function()
		return format.read(src, name)
	end)

	if not ok then
		log(code) -- error
		return false, failurepoint.parsing
	end

	checkpointTime = os.clock()
	log(("Parsed! in %.3f seconds"):format(checkpointTime - checkpointTime2))
	checkpointTime2 = checkpointTime
	if print_ast then
		log("Printing raw AST")
		log(format.lispy_print(code))
		log("End printing raw AST")
	end

	log("Expression -> terms")
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
		log(("Evaluating failed in %.3f seconds"):format(checkpointTime - checkpointTime2))
		log(expr)
		return false, failurepoint.termgen
	end
	return true, expr, env
end

---@param bound_expr inferrable
---@param log function
---@return failurepoint
local function execute_alc_file(bound_expr, log)
	checkpointTime = os.clock()
	log(("Got a term! in %.3f seconds"):format(checkpointTime - checkpointTime2))
	checkpointTime2 = checkpointTime
	if print_inferrable then
		log("bound_expr: (inferrable term follows)")
		log(bound_expr:pretty_print(terms.typechecking_context()))
	end

	log("Inferring")
	if profile_run and profile_what == "infer" then
		profile.start()
	end
	local ok, type, usages, term = pcall(function()
		return evaluator.infer(bound_expr, terms.typechecking_context())
	end)

	if not ok then
		log(type) -- error
		return failurepoint.typechecking
	end

	if profile_run and profile_what == "infer" then
		profile.stop()
		if profile_flame then
			profile.dump_flame(profile_file)
		else
			profile.dump(profile_file)
		end
	end

	checkpointTime = os.clock()
	log(("Inferred! in %.3f seconds"):format(checkpointTime - checkpointTime2))
	checkpointTime2 = checkpointTime
	if print_typed then
		log("type: (value term follows)")
		log(type)
		log("usages:", usages)
		log("term: (typed term follows)")
		log(term:pretty_print(terms.runtime_context()))
	end

	local gen = require "terms-generators"
	local set = gen.declare_set
	local unique_id = gen.builtin_table

	local ok, err = pcall(function()
		evaluator.typechecker_state:flow(
			type,
			nil,
			terms.value.program_type(
				terms.value.effect_row(set(unique_id)(terms.TCState, terms.lua_prog), terms.value.effect_empty),
				evaluator.typechecker_state:metavariable(terms.typechecking_context()):as_value()
			),
			nil,
			"final flow check"
		)
	end)

	if not ok then
		log(err)
		return failurepoint.typechecking
	end

	log("Evaluating")
	local ok, result = pcall(function()
		return evaluator.evaluate(term, terms.runtime_context())
	end)

	if not ok then
		log(result)
		return failurepoint.evaluating
	end

	checkpointTime = os.clock()
	log(("Evaluated! in %.3f seconds"):format(checkpointTime - checkpointTime2))
	checkpointTime2 = checkpointTime
	if print_evaluated then
		log("result: (value term follows)")
		log(result)
	end

	log("Executing")
	local ok, result_exec = pcall(function()
		return evaluator.execute_program(result)
	end)

	if not ok then
		log(result_exec) -- error
		return failurepoint.executing
	end

	checkpointTime = os.clock()
	log(("Executed! in %.3f seconds"):format(checkpointTime - checkpointTime2))
	checkpointTime2 = checkpointTime
	log("result_exec: (value term follows)")
	log(result_exec)

	log(("Runtest succeeded in %.3f seconds"):format(checkpointTime - startTime))

	return failurepoint.success
end

local ok, expr, env = load_alc_file(prelude, env, print)
if not ok then
	return
end
---@cast expr inferrable
---@cast env Environment

if test_harness then
	local test_list_file, err = io.open("testlist.json")
	if not test_list_file then
		error(err)
	end
	---@type { [string]: string }
	local test_list = json.parse(test_list_file:read("a"))

	---@type { [string]: string }
	local logs = {}

	for file, completion in pairs(test_list) do
		logs[file] = ""

		local printrepl = function(...)
			local args = table.pack(...)

			for i = 1, #args do
				args[i] = tostring(args[i])
			end

			logs[file] = logs[file] .. table.concat(args, " ") .. "\n"
		end

		local ok, test_expr, test_env = load_alc_file(file, env, printrepl)
		if not ok then
			if completion == test_expr then
				print("success: " .. file .. ", stopped at " .. test_expr)
			else
				print("\n\nfailure, test " .. file .. " stopped at " .. test_expr .. " \n" .. logs[file] .. "\n\n")
			end
		else
			---@cast test_expr inferrable
			---@cast test_env Environment
			local _, test_expr, _ = test_env:exit_block(test_expr, shadowed)

			local ok = execute_alc_file(test_expr, printrepl)

			if completion == ok then
				print("success: " .. file .. ", stopped at " .. ok)
			else
				print("\n\nfailure, test " .. file .. " stopped at " .. ok .. "\n" .. logs[file] .. "\n\n")
			end
		end
	end
else
	local env, bound_expr, purity = env:exit_block(expr, shadowed)

	execute_alc_file(bound_expr, print)
end
