local metalanguage = require './metalanguage'
local evaluator = require './evaluator'
local format = require './format-adapter'
local base_env = require './base-env'
local p = require 'pretty-print'.prettyPrint
local exprs = require './alicorn-expressions'
local fs = require 'fs'

local src = fs.readFileSync("testfile.alc")
print("read code")
print(src)
print("parsing code")
local code = format.read(src, "inline")
-- p(code)

local env = base_env.create()

print("evaluating")
local ok, expr, env = code:match({exprs.block(metalanguage.accept_handler, env)}, metalanguage.failure_handler, nil)
if not ok then
  p(expr)
  return
end

local type, usages, term = evaluator.infer(expr, env.typechecking_context)
print(type:pretty_print())
p(usages)
print(term:pretty_print())

local result = evaluator.evaluate(term, env.runtime_context)
print(result:pretty_print())