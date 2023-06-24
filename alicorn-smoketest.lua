
local evaluator = require './alicorn-evaluator'
local format = require './format-adapter'
local base_env = require './base-env'

local src = "do (val x = 6) (+ x 3)"
local code = format.read(src, "inline")

print ('code', code)

local env = base_env.create()

local ok, res = evaluator.eval(code, env)

print(ok, res)
