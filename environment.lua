local trie = require "./lazy-prefix-tree"
local fibbuf = require "./fibonacci-buffer"
local U = require "./alicorn-utils"

local terms = require "./terms"
local inferrable_term = terms.inferrable_term
local typechecking_context = terms.typechecking_context
local module_mt = {}

local eval = require "./evaluator"
local infer = eval.infer

local environment_mt

---Takes a table resembling an old environment (can be missing fields, it doesn't matter) and turns it into a new environment
---@param old_env table
---@param opts table?
---@return Environment
local function update_env(old_env, opts)
	local new_env = {}
	if opts then
		for k, v in pairs(opts) do
			new_env[k] = v
		end
	end
	if old_env then
		for k, v in pairs(old_env) do
			if new_env[k] == nil then
				new_env[k] = v
			end
		end
	end
	new_env.locals = new_env.locals or trie.empty
	new_env.nonlocals = new_env.nonlocals or trie.empty
	new_env.in_scope = new_env.nonlocals:extend(new_env.locals)
	new_env.bindings = new_env.bindings or fibbuf()
	new_env.purity = new_env.purity or terms.block_purity.pure
	new_env.perms = new_env.perms or {}
	new_env.typechecking_context = new_env.typechecking_context or typechecking_context()
	return setmetatable(new_env, environment_mt)
end

local new_env = update_env

---@class Environment
---@field typechecking_context TypecheckingContext
---@field locals PrefixTree
---@field nonlocals PrefixTree
---@field in_scope PrefixTree
---@field bindings FibonacciBuffer
---@field purity block_purity
---@field perms table
local environment = {}

---@class ShadowEnvironment
---@field shadowed Environment

---@param name string
---@return boolean
---@return inferrable|string
function environment:get(name)
	local present, binding = self.in_scope:get(name)
	if not present then
		return false, 'symbol "' .. name .. '" is not in scope'
	end
	if binding == nil then
		return false,
			'symbol "'
				.. name
				.. '" is marked as present but with no data; this indicates a bug in the environment or something violating encapsulation'
	end
	return true, binding
end

---@param name string
---@param type value
---@param value value
local function log_binding(name, type, value)
	print("New let binding")
	print("name:", name)
	print("type: (value term follows)")
	print(type)
	print("value: (value term follows)")
	print(value)
end

---@param binding binding
---@return Environment
function environment:bind_local(binding)
	--print("bind_local: (binding term follows)")
	--print(binding:pretty_print(self.typechecking_context))
	if binding:is_let() then
		local name, expr = binding:unwrap_let()
		local expr_type, expr_usages, expr_term = infer(expr, self.typechecking_context)
		if terms.value.value_check(expr_type) ~= true then
			print("expr", expr)
			error("infer returned a bad type for expr in bind_local")
		end
		local n = #self.typechecking_context
		local term = inferrable_term.bound_variable(n + 1)
		local locals = self.locals:put(name, term)
		local evaled = eval.evaluate(expr_term, self.typechecking_context.runtime_context)
		-- print "doing let binding"
		-- print(expr:pretty_print())
		--log_binding(name, expr_type, evaled)
		local typechecking_context = self.typechecking_context:append(name, expr_type, evaled)
		local bindings = self.bindings:append(binding)
		return update_env(self, {
			locals = locals,
			bindings = bindings,
			typechecking_context = typechecking_context,
		})
	elseif binding:is_tuple_elim() then
		local names, subject = binding:unwrap_tuple_elim()
		local subject_type, subject_usages, subject_term = infer(subject, self.typechecking_context)
		--local subject_qty, subject_type = subject_type:unwrap_qtype()
		--DEBUG:
		if subject_type:is_enum_value() then
			print "bad subject infer"
			print(subject:pretty_print(self.typechecking_context))
		end

		-- evaluating the subject is necessary for inferring the type of the body
		local subject_value = U.tag(
			"evaluate",
			{ subject_term = subject_term },
			eval.evaluate,
			subject_term,
			self.typechecking_context:get_runtime_context()
		)
		-- extract subject type and evaled for each elem in tuple
		local tupletypes, n_elements = eval.infer_tuple_type(subject_type, subject_value)

		--local decls
		--[[

		if inner_type:is_tuple_type() then
			decls = subject_type:unwrap_tuple_type()
		elseif inner_type:is_host_tuple_type() then
			decls = subject_type:unwrap_host_tuple_type()
		else
			error("bind_local tuple_elim, subject_type: expected a term with a tuple type, but got " .. subject_type.kind)
		end
		]]

		local typechecking_context = self.typechecking_context
		local n = #typechecking_context
		local locals = self.locals

		if not (n_elements == #names) then
			error("attempted to bind " .. n_elements .. " tuple elements to " .. #names .. " variables")
		end

		for i, v in ipairs(names) do
			--local constructor, arg = decls:unwrap_enum_value()
			-- if constructor ~= "cons" then
			-- 	error("todo: this error message")
			-- end
			local term = inferrable_term.bound_variable(n + i)
			locals = locals:put(v, term)

			local evaled = eval.index_tuple_value(subject_value, i)
			--log_binding(v, tupletypes[i], evaled)
			typechecking_context = typechecking_context:append(v, tupletypes[i], evaled)
		end
		local bindings = self.bindings:append(binding)
		return update_env(self, {
			locals = locals,
			bindings = bindings,
			typechecking_context = typechecking_context,
		})
	elseif binding:is_annotated_lambda() then
		local param_name, param_annotation, anchor, visible = binding:unwrap_annotated_lambda()
		if not anchor or not anchor.sourceid then
			print("binding", binding)
			error "missing anchor for annotated lambda binding"
		end
		local annotation_type, annotation_usages, annotation_term = infer(param_annotation, self.typechecking_context)
		--print("binding lambda annotation: (typed term follows)")
		--print(annotation_term:pretty_print(self.typechecking_context))
		local evaled = eval.evaluate(annotation_term, self.typechecking_context.runtime_context)
		local bindings = self.bindings:append(binding)
		local locals = self.locals:put(param_name, inferrable_term.bound_variable(#self.typechecking_context + 1))
		local typechecking_context = self.typechecking_context:append(param_name, evaled, nil, anchor)
		return update_env(self, {
			locals = locals,
			bindings = bindings,
			typechecking_context = typechecking_context,
		})
		--error "NYI lambda bindings"
	else
		error("bind_local: unknown kind: " .. binding.kind)
	end
	error("unreachable!?")
end

---@class Module
---@field bindings PrefixTree

---@return Environment
---@return Module
function environment:gather_module()
	return self, setmetatable({ bindings = self.locals }, module_mt)
end

---@param module Module
---@return Environment
function environment:open_module(module)
	return new_env {
		locals = self.locals:extend(module.bindings),
		nonlocals = self.nonlocals,
		perms = self.perms,
	}
end

---@param module Module
---@return Environment
function environment:use_module(module)
	return new_env {
		locals = self.locals,
		nonlocals = self.nonlocals:extend(module.bindings),
		perms = self.perms,
	}
end

---@param name string
---@return Environment
function environment:unlet_local(name)
	return new_env {
		locals = self.locals:remove(name),
		nonlocals = self.nonlocals,
		perms = self.perms,
	}
end

---enter a new block, shadowing the current context and allowing new bindings
---@param pure block_purity
---@return ShadowEnvironment
---@return Environment
function environment:enter_block(pure)
	--print "entering block"
	--self.typechecking_context:dump_names()
	eval.typechecker_state:enter_block()
	return { shadowed = self },
		new_env {
			-- locals = nil,
			nonlocals = self.in_scope,
			perms = self.perms,
			typechecking_context = self.typechecking_context,
		}
end

---exit a block, resolving the bindings in that block and restoring the shadowed locals
---@param term inferrable
---@param shadowed ShadowEnvironment
---@return Environment
---@return inferrable
---@return purity
function environment:exit_block(term, shadowed)
	-- -> env, term
	local outer = shadowed.shadowed or error "shadowed.shadowed missing"
	local env = new_env {
		locals = outer.locals,
		nonlocals = outer.nonlocals,
		in_scope = outer.in_scope,
		perms = outer.perms,
		typechecking_context = outer.typechecking_context,
		bindings = outer.bindings,
	}
	--print("exiting block and dropping " .. #self.bindings .. " bindings")
	--self.typechecking_context:dump_names()
	--print "outer"
	--outer.typechecking_context:dump_names()
	--print "new"
	--env.typechecking_context:dump_names()
	local wrapped = term
	for idx = self.bindings:len(), 1, -1 do
		local binding = self.bindings:get(idx)
		if not binding then
			error "missing binding"
		end
		if binding:is_let() then
			local name, expr = binding:unwrap_let()
			wrapped = terms.inferrable_term.let(name, expr, wrapped)
		elseif binding:is_tuple_elim() then
			local names, subject = binding:unwrap_tuple_elim()
			wrapped = terms.inferrable_term.tuple_elim(names, subject, wrapped)
		elseif binding:is_annotated_lambda() then
			local name, annotation, anchor, visible = binding:unwrap_annotated_lambda()
			wrapped = terms.inferrable_term.annotated_lambda(name, annotation, wrapped, anchor, visible)
		end
	end
	eval.typechecker_state:exit_block()

	return env, wrapped
end

environment_mt = { __index = environment }

---@param env Environment
---@return string
local function dump_env(env)
	return "Environment" .. "\nlocals: " .. trie.dump_map(env.locals) .. "\nnonlocals: " .. trie.dump_map(env.nonlocals)
end

return {
	new_env = new_env,
	dump_env = dump_env,
}
