local terms = require './terms'
local exprs = require './alicorn-expressions'

local alc = "2"

local metalanguage = require './metalanguage'
local format = require './format-adapter'
local evaluator = require './evaluator'
local p = require 'pretty-print'.prettyPrint
-- local types = require './typesystem'
local fs = require 'fs'

local src = "2" -- fs.readFileSync("testfile.alc")
print("read code")
print(src)
print("parsing code")
local code = format.read(src, "inline")
p("code", code)

local env = terms.new_env({})
p("env", env)

local ok, expr, env = code:match({exprs.block(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)
p("expr", expr, env)

if not ok then
    return
end

local inferred_type, usage_counts, inferred_term = evaluator.infer(expr, env.typechecking_context)
p("infer", inferred_type, usage_counts, inferred_term)

local evaled = evaluator.evaluate(inferred_term, env.runtime_context)
p("eval", evaled)
-- print("evaluating")
-- local ok, res = evaluator.eval_block(code, env)
-- if ok then
--   print("succeeded")
--   print(res.val .. " : " .. types.type_name(res.type))
-- else
--   print("failed")
--   print(res)
-- end
