-- local gen = require './terms-generators'
-- local terms = require './terms'
-- local eval = require './evaluator'

---

local terms = require './terms'
local exprs = require './alicorn-expressions'

local metalanguage = require './metalanguage'
local format = require './format-adapter'
local gen = require './terms-generators'
local evaluator = require './evaluator'
local environment = require './environment'
local p = require 'pretty-print'.prettyPrint
local trie = require './lazy-prefix-tree'

-- local types = require './typesystem'
local fs = require 'fs'

local src = "+ 621 926" -- fs.readFileSync("testfile.alc")
print("read code")
print(src)
print("parsing code")
local code = format.read(src, "inline")
p("code", code)



local lit = terms.typed_term.literal
local var = terms.typed_term.bound_variable
local lam = terms.typed_term.lambda
local app = terms.typed_term.application

local num = terms.value.number

-- var(1) refers to the outermost bound variable, 2 next outermost, etc
-- as opposed to de bruijn indices, where 1 refers to the innermost (nearest) binding, etc
local id = lam(var(1))
local const = lam(lam(var(1)))
-- in de bruijn indices, these would be lam(var(1)) and lam(lam(var(2))) respectively


local array = gen.declare_array
local usage_array = array(gen.builtin_number)
local inferrable_array = array(terms.inferrable_term)
local typed_array = array(terms.typed_term)

local function unrestricted(t) return terms.value.qtype(terms.value.quantity(terms.quantity.unrestricted), t) end
local function inf_t(t) return terms.inferrable_term.typed(terms.value.star(0), usage_array(), lit(unrestricted(t))) end
local function inf_typ(t, typ) return terms.inferrable_term.typed(unrestricted(t), usage_array(), typ) end
local inf_var = terms.inferrable_term.bound_variable
local inf_app = terms.inferrable_term.application

local value_array = array(terms.value)
local function tup_val(...) return terms.value.tuple_value(value_array(...)) end
local function cons(...) return terms.value.data_value("cons", tup_val(...)) end
p("tup_val!",tup_val())
local empty = terms.value.data_value("empty", tup_val())
local function ctype(t)
  local initial_context = terms.runtime_context()
  return evaluator.evaluate(app(const, lit(t)), initial_context)
end

local t_prim_num = terms.value.prim_number_type
local two_tuple_decl = unrestricted(terms.value.prim_tuple_type(
  cons(
    cons(
      empty,
      ctype(unrestricted(t_prim_num))
    ),
    ctype(unrestricted(t_prim_num))
  )
))
local tuple_decl = unrestricted(terms.value.prim_tuple_type(
  cons(
    empty,
    ctype(unrestricted(t_prim_num))
  )
))


local function prim_f(f) return lit(terms.value.prim(f)) end
local prim_add = prim_f(function(left, right) return left + right end)
local function prim_lit(x) return lit(terms.value.prim(x)) end
local function prim_tup(...) return terms.typed_term.prim_tuple_cons(typed_array(...)) end

local add = prim_f(function(left, right) return left + right end)
local inf_add = inf_typ(terms.value.prim_function_type(two_tuple_decl, tuple_decl), add)
local inf_add_from_primitive_applicative = exprs.primitive_applicative(function(a, b) return a + b end, {t_prim_num, t_prim_num}, {t_prim_num})

print("hoof constructed add:")
print(inf_add:pretty_print())

print("primitive_applicative add:")
print(inf_add_from_primitive_applicative:pretty_print())

local env = environment.new_env({
    nonlocals = trie.empty:put("+", inf_add)
})
local env = environment.new_env({
    nonlocals = trie.empty:put("+", inf_add_from_primitive_applicative)
})

p("env", environment.dump_env(env))

local ok, expr, env = code:match({exprs.block(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)

p("expr", ok, env)
if expr.pretty_print then
    print(expr:pretty_print())
else
    p(expr)
end

if not ok then
    return
end

local inferred_type, usage_counts, inferred_term = evaluator.infer(expr, env.typechecking_context)
p("infer", usage_counts)
print(inferred_type:pretty_print())
print(inferred_term:pretty_print())

local evaled = evaluator.evaluate(inferred_term, env.runtime_context)
p("eval")
print(evaled:pretty_print())
-- print("evaluating")
-- local ok, res = evaluator.eval_block(code, env)
-- if ok then
--   print("succeeded")
--   print(res.val .. " : " .. types.type_name(res.type))
-- else
--   print("failed")
--   print(res)
-- end
