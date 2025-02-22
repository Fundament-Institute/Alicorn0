-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

require("lua-init")

--local endTime = os.time() + 3
--while os.time() < endTime do end

require "pretty-printer" -- has side-effect of loading global p()

local startTime = os.clock()
local checkpointTime = startTime
local checkpointTime2 = startTime
local metalanguage = require "metalanguage"
local evaluator = require "evaluator"
local format = require "format-adapter"
local format_ = require "format"
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
	local file_n = getopt(process.argv, { ["?"] = function() end }, {})
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
local reload_mode = false
local test_single = false
local test_name = ""
local print_usage = false
local short_opts = {
	["S"] = function(_opt_repr)
		print_src = true
	end,
	["f"] = function(_opt_repr)
		print_ast = true
	end,
	["s"] = function(_opt_repr)
		print_inferrable = true
	end,
	["t"] = function(_opt_repr)
		print_typed = true
	end,
	["v"] = function(_opt_repr)
		print_evaluated = true
	end,
	["r:"] = function(opt_repr, arg)
		reload_mode = true
		test_name = arg
	end,
	["p:"] = function(opt_repr, arg)
		profile_run = true
		local subargs = U.split_commas(arg)
		profile_file = subargs[1]
		profile_what = subargs[2] or "match"
	end,
	["P:"] = function(opt_repr, arg)
		profile_run = true
		profile_flame = true
		local subargs = U.split_commas(arg)
		profile_file = subargs[1]
		profile_what = subargs[2] or "match"
	end,
	["T:"] = function(opt_repr, arg)
		test_single = true
		test_name = arg
	end,
	["?"] = function(_opt_repr)
		print_usage = true
	end,
}
local long_opts = {
	["help"] = "?",
	["print-src"] = "S",
	["print-ast"] = "f",
	["print-inferrable"] = "s",
	["print-typed"] = "t",
	["print-evaluated"] = "v",
	["reload"] = "r",
	["profile"] = "p",
	["flamegraph"] = function(_opt_repr)
		profile_flame = true
	end,
	["no-flamegraph"] = function(_opt_repr)
		profile_flame = false
	end,
	["test"] = "T",
}
local first_operand = getopt(argv, short_opts, long_opts)

if print_usage then
	local usage = [=[Usage: %s [-Sfstv] [(-p|-P) <file>[,<what>]] [-T <test>]
  -S, --print-source
          Print the Alicorn source code about to be tested.
          (mnemonic: Source)
  -f, --print-ast
          Show the AST generated from the source code.
          (mnemonic: format.read)
  -s, --print-inferrable
          Show the unchecked term. *
          (mnemonic: syntax:match)
  -t, --print-typed
          Show the type-checked term. *
          (mnemonic: typed)
  -v, --print-evaluated
          Show the evaluated term. *
          (mnemonic: value)

          * Some type-checking and evaluation may happen during the course of
          producing a top-level term, due to the dependent nature of Alicorn.
  -p, --profile <file>[,<what>]
          Run a profile over the test and output the trace to a file.
          (mnemonic: profile)
          what = match: Profile syntax:match.    [default]
          what = infer: Profile evaluator.infer.
          Works best in conjunction with -T.
      --[no-]flamegraph
          Enable or disable outputting a flamegraph-compatible trace when profiling.
  -P <file>[,<what>]
          Like -p, but enable outputting a flamegraph-compatible trace.
          (mnemonic: Phlame! :P)
  -T, --test <file>
          Choose a specific test to run.
          (mnemonic: Test)
          Without -T, all tests in testlist.json are run.
]=]
	io.stderr:write(usage:format(argv[0]))
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
---@return failurepoint | anchored_inferrable
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
		io.stderr:write(src, "\n")
	end

	log("Parsing code")
	local ok, code = pcall(function()
		return U.notail(format.read(src, name))
	end)

	if not ok then
		log(code) -- error
		return false, failurepoint.parsing
	end

	checkpointTime = os.clock()
	log(("Parsed! in %.3f seconds"):format(checkpointTime - checkpointTime2))
	checkpointTime2 = checkpointTime
	if print_ast then
		io.stderr:write("Printing raw AST\n")
		io.stderr:write(format.lispy_print(code), "\n")
		io.stderr:write("End printing raw AST\n")
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

---@param bound_expr anchored_inferrable
---@param log function
---@param env Environment
---@return failurepoint
local function execute_alc_file(bound_expr, log, env)
	checkpointTime = os.clock()
	log(("Got a term! in %.3f seconds"):format(checkpointTime - checkpointTime2))
	checkpointTime2 = checkpointTime
	if print_inferrable then
		io.stderr:write("bound_expr: (inferrable term follows)\n")
		io.stderr:write(bound_expr:pretty_print(env.typechecking_context), "\n")
	end

	log("Inferring")
	if profile_run and profile_what == "infer" then
		profile.start()
	end
	local ok, type, usages, term = pcall(function()
		local ok, type, usages, term = evaluator.infer(bound_expr, env.typechecking_context)
		if not ok then
			error(type)
		end
		return type, usages, term
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
		io.stderr:write("type: (value term follows)\n")
		io.stderr:write(tostring(type), "\n")
		io.stderr:write("usages: ", tostring(usages), "\n")
		io.stderr:write("term: (typed term follows)\n")
		io.stderr:write(term:pretty_print(env.typechecking_context.runtime_context), "\n")
	end

	local gen = require "terms-generators"
	local set = gen.declare_set
	local unique_id = gen.builtin_table

	local ok, err = pcall(function()
		local ok, err = evaluator.typechecker_state:flow(
			type,
			env.typechecking_context,
			terms.flex_value.program_type(
				terms.flex_value.effect_row(terms.unique_id_set(terms.TCState, terms.lua_prog)),
				evaluator.typechecker_state:metavariable(env.typechecking_context):as_flex()
			),
			env.typechecking_context,
			terms.constraintcause.primitive("final flow check", format_.anchor_here())
		)

		if not ok then
			error(tostring(err))
		end
	end)

	if not ok then
		log(err)
		return failurepoint.typechecking
	end

	log("Evaluating")
	local ok, result = pcall(function()
		return U.notail(evaluator.evaluate(term, env.typechecking_context.runtime_context, env.typechecking_context))
	end)

	if not ok then
		log(result)
		return failurepoint.evaluating
	end

	checkpointTime = os.clock()
	log(("Evaluated! in %.3f seconds"):format(checkpointTime - checkpointTime2))
	checkpointTime2 = checkpointTime
	if print_evaluated then
		io.stderr:write("result: (value term follows)\n")
		io.stderr:write(tostring(result), "\n")
	end

	log("Executing")
	local ok, result_exec = pcall(function()
		return U.notail(evaluator.execute_program(result))
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

-- local graph_backtrace = 5
local internal_state

local function dump_edges(edge_list)
	if internal_state == nil then
		local internals_interface = require "internals-interface"

		internal_state = internals_interface.evaluator.typechecker_state
	end

	local function dump_edge(l, r)
		local function dump_edge_from(l, r, edges)
			for _, v in ipairs(edges) do
				if v.left == l and v.right == r then
					print("EDGE FOUND: " .. l .. "->" .. r)
					v.cause.track = true
					print("CAUSED BY: " .. tostring(v.cause))
				end
			end
		end
		dump_edge_from(l, r, internal_state.graph.constrain_edges:all())
		dump_edge_from(l, r, internal_state.graph.leftcall_edges:all())
		dump_edge_from(l, r, internal_state.graph.rightcall_edges:all())
	end

	for i, v in ipairs(edge_list) do
		print("Searching for: " .. v[1] .. "->" .. v[2])
		dump_edge(v[1], v[2])
	end
end

if graph_backtrace ~= nil then
	local internals_interface = require "internals-interface"

	internal_state = internals_interface.evaluator.typechecker_state
	internal_state.snapshot_count = graph_backtrace -- Store last [backtrack] snapshots
	internal_state.snapshot_buffer = {}
end

local function serialize_graph(name)
	local internals_interface = require "internals-interface"

	internal_state = internals_interface.evaluator.typechecker_state

	local f = io.open(name, "w")
	for i, v in ipairs(internal_state.values) do
		f:write(i, "=", U.strip_ansi(v[1]:pretty_print(v[3])):gsub("\n", "\\n"), "\n")
	end

	local function serialize_edges(edges)
		f:write("\n")
		for _, v in ipairs(edges) do
			f:write(v.left, "=", v.right, "\n")
		end
	end
	serialize_edges(internal_state.graph.constrain_edges:all())
	serialize_edges(internal_state.graph.leftcall_edges:all())
	serialize_edges(internal_state.graph.rightcall_edges:all())
	f:close()
end

local env = base_env.create()

local prelude_env, env = env:enter_block(terms.block_purity.effectful)

local ok, expr, env = load_alc_file(prelude, env, print)
if not ok then
	if graph_backtrace ~= nil then
		local snapshots = internal_state.snapshot_buffer
		local i = (internal_state.snapshot_count + 1) % graph_backtrace
		local slice = {}
		for j = 2, graph_backtrace do
			local f = io.open("GRAPH_STATE" .. j .. ".dot", "w")
			local additions = internal_state:Visualize(f, snapshots[i + 1], snapshots[i + 2], slice)
			f:close()
			i = (i + 1) % graph_backtrace
			for i, v in ipairs(additions) do
				slice[v] = v
			end
		end
	end

	return
end

---@cast expr anchored_inferrable
---@cast env Environment

---@param file string
---@param completion string
---@param env Environment
---@return boolean
---@return string
local function perform_test(file, completion, env)
	local shadowed, test_env = env:enter_block(terms.block_purity.effectful)
	local log = ""

	local printrepl = function(...)
		local args = table.pack(...)

		for i = 1, #args do
			args[i] = tostring(args[i])
		end

		log = log .. table.concat(args, " ") .. "\n"
	end

	local ok, test_expr, test_env = load_alc_file(file, test_env, printrepl)
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
		---@cast test_expr anchored_inferrable
		---@cast test_env Environment
		local test_env, test_expr, _ = test_env:exit_block(test_expr, shadowed)

		local ok = execute_alc_file(test_expr, printrepl, test_env)

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

if reload_mode then
	while true do
		print("Loading " .. test_name)
		evaluator.typechecker_state:speculate(function()
			local shadowed, test_env = env:enter_block(terms.block_purity.effectful)
			local ok, test_expr, test_env = load_alc_file(test_name, test_env, print)

			if ok then
				---@cast test_expr anchored_inferrable
				---@cast test_env Environment
				local test_env, test_expr, _ = test_env:exit_block(test_expr, shadowed)

				local ok = execute_alc_file(test_expr, print, test_env)
			end

			return false
		end)

		print("Continue? y/n: ")
		if io.read(1) == "n" then
			return
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

			-- We do not attempt to capture errors here because no test should cause an internal compiler error, only recoverable errors.
			-- If a shadowing error occurs, it means a test caused an internal compiler error that was captured by the syntax that left
			-- the tests in a bad state.
			evaluator.typechecker_state:speculate(function()
				local ok, log = perform_test(file, completion, env)

				logs[file] = log
				if not ok then
					U.append(failures, file)
				end

				return false
			end)
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
	local env, bound_expr, purity = env:exit_block(expr, prelude_env)

	execute_alc_file(bound_expr, print)
end
