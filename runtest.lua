local jit_enabled = true
local lldebugger_enabled = os.getenv("LOCAL_LUA_DEBUGGER_VSCODE") == "1"
if lldebugger_enabled then
	jit_enabled = false
end

if jit then
	if jit_enabled then
		jit.opt.start("maxtrace=10000")
		jit.opt.start("maxmcode=4096")
		jit.opt.start("recunroll=5")
		jit.opt.start("loopunroll=60")
	else
		jit.off()
	end
end

if lldebugger_enabled then
	require("lldebugger").start(true)
end

--local endTime = os.time() + 3
--while os.time() < endTime do end

require "pretty-printer" -- has side-effect of loading global p()

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
local U = require "alicorn-utils"

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
	io.stderr:write("Missing or unknown arg table! Using stub\n")
	interpreter_argv = { [0] = "lua" }
	argv = { [0] = "runtest.lua" }
end
local test_harness = true
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
local test_single = false
local test_name = ""
local print_usage = false
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
		local subargs = U.split_commas(arg)
		profile_file = subargs[1]
		profile_what = subargs[2] or "match"
	end,
	["P:"] = function(_, arg)
		if not arg then
			error("-P requires a file argument")
		end
		profile_run = true
		profile_flame = true
		local subargs = U.split_commas(arg)
		profile_file = subargs[1]
		profile_what = subargs[2] or "match"
	end,
	["T:"] = function(_, arg)
		if not arg then
			error("-T requires a test argument")
		end
		test_single = true
		test_name = arg
	end,
	["?"] = function(c)
		print_usage = true
	end,
}
local first_operand = getopt(argv, opttab)

if print_usage then
	io.stderr:write(("Usage: %s [-Sfstv] [-p file[,what] | -P file[,what]] [-T test]\n"):format(argv[0]))
	io.stderr:write("  -S  Print the Alicorn source code about to be tested.\n")
	io.stderr:write("      (mnemonic: Source)\n")
	io.stderr:write("  -f  Show the AST generated from the source code.\n")
	io.stderr:write("      (mnemonic: format.read)\n")
	io.stderr:write("  -s  Show the unchecked term. *\n")
	io.stderr:write("      (mnemonic: syntax:match)\n")
	io.stderr:write("  -t  Show the type-checked term. *\n")
	io.stderr:write("      (mnemonic: typed)\n")
	io.stderr:write("  -v  Show the evaluated term. *\n")
	io.stderr:write("      (mnemonic: value)\n")
	io.stderr:write("      * Some type-checking and evaluation may happen during the course of\n")
	io.stderr:write("        producing a top-level term, due to the dependent nature of Alicorn.\n")
	io.stderr:write("  -p  Run a profile over the test and output the trace to a file.\n")
	io.stderr:write("      (mnemonic: profile)\n")
	io.stderr:write("      what = match: Profile syntax:match.    [default]\n")
	io.stderr:write("      what = infer: Profile evaluator.infer.\n")
	io.stderr:write("      Works best in conjunction with -T.\n")
	io.stderr:write("  -P  Like -p, but output a flamegraph-compatible trace.\n")
	io.stderr:write("      (mnemonic: Phlame! :P)\n")
	io.stderr:write("  -T  Choose a specific test to run.\n")
	io.stderr:write("      (mnemonic: Test)\n")
	io.stderr:write("      Without -T, all tests in testlist.json are run.\n")
	os.exit()
end

io.write("Interpreter  : ", table.concat(interpreter_argv, " ", 0), "\n")
io.write("File         : ", argv[0], "\n")
io.write("Options      : ", table.concat(argv, " ", 1, first_operand - 1), "\n")
io.write("Operands     : ", table.concat(argv, " ", first_operand), "\n")
if profile_run then
	io.write("Profile flame? ", tostring(profile_flame), "\n")
	io.write("Profile file : ", profile_file, "\n")
	io.write("Profile what : ", profile_what, "\n")
end

local prelude = "prelude.alc"

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
			terms.constraintcause.primitive("final flow check", format.create_anchor(0, 0, "<NIL>"))
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

--local graph_backtrace = 5
local internal_state
if graph_backtrace ~= nil then
	local internals_interface = require "internals-interface"

	internal_state = internals_interface.evaluator.typechecker_state
	internal_state.snapshot_count = graph_backtrace -- Store last [backtrack] snapshots
	internal_state.snapshot_buffer = {}
end

local ok, expr, env = load_alc_file(prelude, env, print)
if not ok then
	if graph_backtrace ~= nil then
		local snapshots = internal_state.snapshot_buffer
		local i = (internal_state.snapshot_count + 1) % graph_backtrace
		local slice = {}
		for j = 2, graph_backtrace do
			local f = io.open("GRAPH_STATE" .. j .. ".dot", "w")
			local out, additions = internal_state:Visualize(snapshots[i + 1], snapshots[i + 2], slice)
			f:write(out)
			f:close()
			i = (i + 1) % graph_backtrace
			slice = additions
		end
	end

	return
end
---@cast expr inferrable
---@cast env Environment

---@param file string
---@param completion string
---@param shadowed ShadowEnvironment
---@param env Environment
---@return boolean
---@return string
local function perform_test(file, completion, shadowed, env)
	local log = ""

	local printrepl = function(...)
		local args = table.pack(...)

		for i = 1, #args do
			args[i] = tostring(args[i])
		end

		log = log .. table.concat(args, " ") .. "\n"
	end

	local ok, test_expr, test_env = load_alc_file(file, env, printrepl)
	if not ok then
		if completion == test_expr then
			io.write(U.outputGreen("success: " .. file .. " stopped at " .. test_expr), "\n")
			return true, log
		else
			io.write(
				"\n\n",
				U.outputRed("failure: " .. file .. " stopped at " .. test_expr .. " (expected " .. completion .. ")"),
				"\n",
				log,
				"\n\n"
			)
			return false, log
		end
	else
		---@cast test_expr inferrable
		---@cast test_env Environment
		local _, test_expr, _ = test_env:exit_block(test_expr, shadowed)

		local ok = execute_alc_file(test_expr, printrepl)

		if completion == ok then
			io.write(U.outputGreen("success: " .. file .. " stopped at " .. ok), "\n")
			return true, log
		else
			io.write(
				"\n\n",
				U.outputRed("failure: " .. file .. " stopped at " .. ok .. " (expected " .. completion .. ")"),
				"\n",
				log,
				"\n\n"
			)
			return false, log
		end
	end
end

if test_harness then
	local test_list_file, err = io.open("testlist.json")
	if not test_list_file then
		error(err)
	end
	local test_list, pos, err = json.decode(test_list_file:read("a"), 1, nil)
	---@cast test_list table

	if err ~= nil then
		print("Couldn't decode JSON describing tests! " .. tostring(err))
		return
	end

	---@type { [string]: string }
	local logs = {}
	local total = 0
	local failures = {}

	for file, completion in pairs(test_list) do
		if (not test_single) or (test_single and file == test_name) then
			total = total + 1
			local ok, log = perform_test(file, completion, shadowed, env)
			logs[file] = log
			if not ok then
				U.append(failures, file)
			end
		end
	end

	if #failures == 0 then
		io.write("All " .. tostring(total) .. " tests passed!\n")
	else
		io.write(tostring(total - #failures) .. " out of " .. tostring(total) .. " tests passed. Failures:\n")
		for _, v in ipairs(failures) do
			io.write("- " .. v .. "\n")
		end
	end
else
	local env, bound_expr, purity = env:exit_block(expr, shadowed)

	execute_alc_file(bound_expr, print)
end
