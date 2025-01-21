local U = require "alicorn-utils"
local terms = require "terms"
local exprs = require "alicorn-expressions"

local metalanguage = require "metalanguage"
local format = require "format-adapter"
local gen = require "terms-generators"
local evaluator = require "evaluator"
local environment = require "environment"
local trie = require "lazy-prefix-tree"

local src = "+ 621 926" -- fs.readFileSync("testfile.alc")
print("read code")
print(src)
print("parsing code")
local code = format.read(src, "inline")
p("code", code)

local lit = terms.typed_term.literal

local array = gen.declare_array
local usage_array = array(gen.builtin_number)

local function inf_typ(t, typ)
	return U.notail(terms.unanchored_inferrable_term.typed(terms.typed_term.literal(t), usage_array(), typ))
end

local value_array = array(terms.value)
local function tup_val(...)
	return U.notail(terms.value.tuple_value(value_array(...)))
end
local function cons(...)
	return U.notail(terms.value.enum_value("cons", tup_val(...)))
end
p("tup_val!", tup_val())
local empty = terms.value.enum_value("empty", tup_val())

local t_host_num = terms.strict_value.host_number_type
local two_tuple_desc = terms.value.host_tuple_type(
	cons(cons(empty, evaluator.const_combinator(t_host_num)), evaluator.const_combinator(t_host_num))
)
local tuple_desc = terms.value.host_tuple_type(cons(empty, evaluator.const_combinator(t_host_num)))

local function host_f(f)
	return U.notail(lit(terms.value.host_value(f)))
end

local add = host_f(function(left, right)
	return U.notail(left + right)
end)
local result_info_pure = terms.strict_value.result_info(terms.result_info(terms.purity.pure))
local inf_add = inf_typ(terms.value.host_function_type(two_tuple_desc, tuple_desc, result_info_pure), add)
local inf_add_from_host_applicative = exprs.host_applicative(function(a, b)
	return U.notail(a + b)
end, { t_host_num, t_host_num }, { t_host_num })

print("hoof constructed add:")
print(inf_add:pretty_print())

print("host_applicative add:")
print(inf_add_from_host_applicative:pretty_print())

-- inf_add_from_host_applicative should be equivalent to hoof constructed inf_add

local env = environment.new_env({
	nonlocals = trie.empty:put("+", inf_add_from_host_applicative),
})

p("env", environment.dump_env(env))

local ok, expr, env = code:match({ exprs.block(metalanguage.accept_handler, env) }, metalanguage.failure_handler, nil)

p("expr", ok, env)
if expr.pretty_print then
	print(expr:pretty_print())
else
	p(expr)
end

if not ok then
	return
end

local ok, inferred_type, usage_counts, inferred_term = evaluator.infer(expr, env.typechecking_context)
if not ok then
	error(tostring(inferred_type))
end
p("infer", usage_counts)
print(inferred_type:pretty_print())
print(inferred_term:pretty_print())

local evaled = evaluator.evaluate(inferred_term, env.runtime_context, env.typechecking_context)
p("eval")
print(evaled:pretty_print())
