
local evaluator = require './alicorn-evaluator'
local format = require './format-adapter'
local base_env = require './base-env'
local p = require 'pretty-print'.prettyPrint
local types = require './typesystem'
local fs = require 'fs'

local src = fs.readFileSync("testfile.alc")
print("read code")
print(src)
print("parsing code")
local code = format.read(src, "inline")
-- p(code)

local env = base_env.create()

print("evaluating")
local ok, res = evaluator.eval_block(code, env)
if ok then
  print("succeeded")
  print(res.val .. " : " .. types.type_name(res.type))
else
  print("failed")
  print(res)
end
