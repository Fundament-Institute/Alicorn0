local evaluator = require "./evaluator"
local profile, profile_n, profile_samples

local function start()
	profile = require("jit.profile")
	profile_n = 0
	profile_samples = {}
	profile.start("li10", function(thread, samples, vmstate)
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
			local term, context, goal, inferred_type
			if infer or check then
				_, term = debug.getlocal(thread, i, 1)
				_, context = debug.getlocal(thread, i, 2)
			end
			if check then
				_, goal = debug.getlocal(thread, i, 3)
				_, inferred_type = debug.getlocal(thread, i, 5)
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
				inferred_type = inferred_type,
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

local function stop()
	profile.stop()
end

local function dump(profile_file)
	local profile_out = io.open(profile_file, "w")
	if not profile_out then
		error("opening profile file failed!")
	end
	for n, sample in ipairs(profile_samples) do
		profile_out:write("sample: ", n, "\n")
		local t = false
		for _, d in ipairs(sample.stack) do
			local depth = sample.stack_n - d.i
			profile_out:write(
				string.format("%d %s %s %s: %s:%d\n", depth, d.what, d.namewhat, d.name, d.source, d.currentline)
			)
			if not t and (d.infer or d.check) then
				profile_out:write(d.context:format_names())
				profile_out:write(d.term:pretty_print(d.context), "\n")
				profile_out:write(d.term:default_print(), "\n")
				if d.check then
					profile_out:write(d.goal:pretty_print(d.context), "\n")
					profile_out:write(d.goal:default_print(), "\n")
					profile_out:write(d.inferred_type:pretty_print(d.context), "\n")
					profile_out:write(d.inferred_type:default_print(), "\n")
				end
				t = true
			end
		end
	end
	profile_out:close()
end

local function dump_flame(profile_file)
	local profile_out = io.open(profile_file, "w")
	if not profile_out then
		error("opening profile file failed!")
	end
	for _, sample in ipairs(profile_samples) do
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

return {
	start = start,
	stop = stop,
	dump = dump,
	dump_flame = dump_flame,
}
