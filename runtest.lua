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
local profile, profile_n, profile_samples
if profile_run then
	profile = require("jit.profile")
	profile_n = 0
	profile_samples = {}
	profile.start("li100", function(thread, samples, vmstate)
		local stack_n = 0
		local stack = {}
		-- luajit's profiler loops from 0 to 100
		-- hopefully 1000 will be enough for us for a while
		for i = 0, 1000 do
			local d = debug.getinfo(thread, i, "Sfln")
			if not d then
				break
			end
			local infer = d.func == evaluator.infer
			local check = d.func == evaluator.check
			local term, context, goal
			if infer or check then
				_, term = debug.getlocal(thread, i, 1)
				_, context = debug.getlocal(thread, i, 2)
			end
			if check then
				_, goal = debug.getlocal(thread, i, 3)
			end
			stack_n = stack_n + 1
			stack[stack_n] = {
				i = i,
				name = d.name,
				namewhat = d.namewhat,
				source = d.source,
				short_src = d.short_src,
				linedefined = d.linedefined,
				lastlinedefined = d.lastlinedefined,
				what = d.what,
				currentline = d.currentline,
				func = d.func,
				infer = infer,
				check = check,
				term = term,
				context = context,
				goal = goal,
			}
		end
		profile_n = profile_n + 1
		profile_samples[profile_n] = {
			stack_n = stack_n,
			stack = stack,
			samples = samples,
			vmstate = vmstate,
		}
	end)
end
local type, usages, term = evaluator.infer(bound_expr, terms.typechecking_context())
if profile_run then
	profile.stop()
	local profile_out = io.open(profile_file, "w")
	for n, sample in ipairs(profile_samples) do
		local s = sample.stack
		for i = sample.stack_n, 1, -1 do
			local d = s[i]
			profile_out:write(string.format("%s %s %s: %s:%d", d.what, d.namewhat, d.name, d.source, d.currentline))
			if i > 1 then
				profile_out:write(";")
			end
		end
		profile_out:write(" ", sample.samples, "\n")
	end
	profile_out:close()
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
