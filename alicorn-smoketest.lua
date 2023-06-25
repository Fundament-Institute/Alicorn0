
local evaluator = require './alicorn-evaluator'
local format = require './format-adapter'
local base_env = require './base-env'
local p = require 'pretty-print'.prettyPrint

local src = "do (val x = 6) (+ x 3)"
print("read code")
print(src)
print("parsing code")
local code = format.read(src, "inline")
-- p(code)

local env = base_env.create()

print("evaluating")
local ok, res = evaluator.eval(code, env)
if ok then
  print("succeeded")
  print(res.val .. " : " .. res.type.kind)
else
  print("failed")
  print(res)
end
