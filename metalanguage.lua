

local env_mt
env_mt = {
  __add = function(self, other)
    local res = {}
    for k, v in pairs(self.dict) do
      res[k] = v
    end
    for k, v in pairs(other.dict) do
      if res[k] ~= nil then
        error("names in environments being merged must be disjoint, but both environments have " .. k)
      end
      res[k] = v
    end
    return setmetatable({dict = res}, env_mt)
  end,
  __index = {
    get = function(self, name)
      return self.dict[name]
    end,
    without = function(self, name)
      local res = {}
      for k, v in pairs(self.dict) do
        if k ~= name then
          res[k] = v
        end
      end
      return setmetatable({dict = res}, env_mt)
    end
  },
  __tostring = function(self)
    local message = "env{"
    local fields = {}
    for k, v in pairs(self.dict) do
      fields[#fields + 1] = tostring(k) .. " = " .. tostring(v)
    end
    message = message .. table.concat(fields, ", ") .. "}"
    return message
  end
}

local function newenv(dict)
  return setmetatable({dict = dict}, env_mt)
end

local syntax_check_reductions = {}

local function symbolenvhandler(env, name)
  --print("symbolenvhandler(", name, env, ")")
  local res = env:get(name)
  if res ~= nil then
    return true, res
  else
    return false, "environment does not contain a binding for " .. name
  end
end

local function symbolexacthandler(expected, name)
  if name == expected then
    return true
  else
    return false, "symbol is expected to be exactly " .. expected .. " but was instead " .. name
  end
end

local function accept_handler(data, ...)
  return true, ...
end
local function failure_handler(data, exception)
  return false, exception
end

function syntax_check_reductions.SymbolInEnvironment(syntax, matcher)
  --print("in symbol in environment reducer", matcher.kind, matcher[1], matcher)
  return syntax:match(
    {
      {
        kind = "Symbol",
        handler = symbolenvhandler
      },
    },
    failure_handler,
    matcher[1]
  )
end

function syntax_check_reductions.SymbolExact(syntax, matcher)
  return syntax:match(
    {
      {
        kind = "Symbol",
        handler = symbolexacthandler
      }
    },
    failure_handler,
    matcher[1]
  )
end

local syntax_error_mt = {
  __tostring = function(self)
    local message = "Syntax error at anchor " .. (self.anchor or "<unknown position>") .. " must be acceptable for one of:\n"
    local options = {}
    for k, v in ipairs(self.matchers) do
      options[k] = v.kind
    end
    message = message .. table.concat(options, ", ")
    message = message .. "\nbut was rejected"
    if self.cause then
      message = message .. " because:\n" .. tostring(self.cause)
    end
    return message
  end
}

local function syntax_error(matchers, anchor, cause)
  return setmetatable(
    {
      matchers = matchers,
      anchor = anchor,
      cause = cause
    },
    syntax_error_mt
  )
end

local constructed_syntax_mt = {
  __index = {
    match = function(self, matchers, unmatched, extra)
      if matchers.kind then print(debug.traceback()) end
      local lasterr = nil
      for _, matcher in ipairs(matchers) do
        if self.accepters[matcher.kind] then
          --print("accepting primitive handler on kind", matcher.kind)
          return self.accepters[matcher.kind](self, matcher, extra)
        elseif syntax_check_reductions[matcher.kind] then
          --print("trying syntax reduction on kind", matcher.kind)
          local res = {syntax_check_reductions[matcher.kind](self, matcher)}
          if res[1] then
            --print("accepted syntax reduction")
            if not matcher.handler then
              print("missing handler for ", matcher.kind, debug.traceback())
            end
            return matcher.handler(extra, table.unpack(res, 2))
          end
          --print("rejected syntax reduction")
          lasterr = res[2]
        end
        --print("rejected syntax kind", matcher.kind)
      end
      return unmatched(extra, syntax_error(matchers, self.anchor, lasterr))
    end
  }
}
local function cons_syntax(accepters, ...)
  return setmetatable({accepters = accepters, ...}, constructed_syntax_mt)
end

local pair_accepters = {
  Pair = function(self, matcher, extra)
    return matcher.handler(extra, self[1], self[2])
  end
}

local function pair(a, b)
  return cons_syntax(pair_accepters, a, b)
end

local symbol_accepters = {
  Symbol = function(self, matcher, extra)
    return matcher.handler(extra, self[1])
  end
}

local function symbol(name)
  return cons_syntax(symbol_accepters, name)
end

local value_accepters = {
  Value = function(self, matcher, extra)
    return matcher.handler(extra, self[1])
  end
}

local function value(val)
  return cons_syntax(value_accepters, val)
end

local nil_accepters = {
  Nil = function(self, matcher, extra)
    return matcher.handler(extra)
  end
}

local nilval = cons_syntax(nil_accepters)

local function list(a, ...)
  if a == nil then return nilval end
  return pair(a, list(...))
end

local eval

local vau_mt = {
  __index = {
    apply = function(self, ops, env)
      local bodyenv = self.params:argmatch(ops) + self.envparam:argmatch(env)
      local bodycode = self.body
      local expr
      local res
      while bodycode ~= unit do
        expr, bodycode = bodycode[1], bodycode[2]
        res, bodyenv = eval(expr, bodyenv)
      end
      return {kind = "value", res}
    end

  }
}

local eval

local function eval_passhandler(env, val)
  --print("eval pass handler", val, env)
  return true, val, env
end

local function eval_pairhandler(env, a, b)
  --print("in eval pairhandler", a, b, env)
  local ok, combiner, _ =
    a:match(
      {
        {
          kind = "Eval",
          env,
          handler = eval_passhandler
        },
      },
      failure_handler,
      env
    )
  if not ok then return false, combiner end
  local ok, val, newenv = combiner:apply(b, env)
  --print("eval pair", ok, val, newenv)
  return ok, val, newenv
end

function eval(syntax, environment)
  return syntax:match(
    {
      {
        kind = "SymbolInEnvironment",
        environment,
        handler = eval_passhandler
      },
      {
        kind = "Value",
        handler = eval_passhandler
      },
      {
        kind = "Pair",
        handler = eval_pairhandler
      }
    },
    failure_handler,
    environment
  )
end

function syntax_check_reductions.Eval(syntax, matcher)
  return eval(syntax, matcher[1])
end


local function syntax_args_val_handler(_, val, newenv)
  return true, val, newenv
end

local function syntax_args_pair_handler(env, a, b)
  local ok, val, _ =
    a:match(
      {
        {
          kind = "Eval",
          env,
          handler = syntax_args_val_handler
        },
      },
      failure_handler,
      nil
    )
  --print("args pair handler", ok, val, _, b)
  return true, true, val, b
end

local function syntax_args_nil_handler(data)
  return true, false
end

function syntax_check_reductions.EvalArgs(syntax, matcher)
  local args = {}
  local ok, ispair, val, tail = true, true, nil, nil
  while ok and ispair do
    ok, ispair, val, tail =
      syntax:match(
        {
          {
            kind = "Pair",
            handler = syntax_args_pair_handler
          },
          {
            kind = "Nil",
            handler = syntax_args_nil_handler
          }
        },
        failure_handler,
        matcher[1]
      )
    if not ok then return false, ispair end
    if ispair then
      args[#args + 1] = val
      syntax = tail
    end
  end
  return true, args
end


local function list_match_pair_handler(rule, a, b)
  --print("list pair handler", a, b, rule)
  local ok, val = a:match({rule}, failure_handler, nil)
  return ok, val, b
end


function syntax_check_reductions.ListMatch(syntax, matcher)
  local args = {}
  local ok, val, tail = true, true, nil
  for i, rule in ipairs(matcher) do
    ok, val, tail =
      syntax:match(
        {
          {
            kind = "Pair",
            handler = list_match_pair_handler,
          }
        },
        failure_handler,
        rule
      )
    --print("list match rule", ok, val, tail)
    if not ok then return false, val end
    args[#args + 1] = val
    syntax = tail
  end
  ok, err =
    syntax:match(
      {
        {
          kind = "Nil",
          handler = accept_handler
        }
      },
      failure_handler,
      nil
    )
  if not ok then return false, err end
  return true, table.unpack(args)
end

local primitive_applicative_mt = {
  __index = {
    apply = function(self, ops, env)
      local ok, args =
        ops:match(
          {
            {
              kind = "EvalArgs",
              env,
              handler = accept_handler
            }
          },
          failure_handler,
          nil
        )
      local res = self.fn(table.unpack(args))
      return true, value(res), env
    end
  }
}

local function primitive_applicative(fn)
  return setmetatable({fn = fn}, primitive_applicative_mt)
end

local primitive_operative_mt = {
  __index = {
    apply = function(self, ops, env)
      return self.fn(ops, env)
    end
  }
}

local function primitive_operative(fn)
  return setmetatable({fn = fn}, primitive_operative_mt)
end

return {
  newenv = newenv,
  accept_handler = accept_handler,
  failure_handler = failure_handler,
  pair = pair,
  symbol = symbol,
  value = value,
  list = list,
  nilval = nilval,
  eval = eval,
  primitive_applicative = primitive_applicative,
  primitive_operative = primitive_operative
}
