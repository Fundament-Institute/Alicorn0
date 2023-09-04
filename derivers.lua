local eq = {
  record = function(t, info)
    local kind = info.kind
    local params = info.params

    local checks = {}
    for i, param in ipairs(params) do
      checks[i] = string.format("left[%q] == right[%q]", param, param)
    end
    local all_checks = table.concat(checks, " and ")
    local chunk = "return function(left, right) return " .. all_checks .. " end"

    print("derive eq: record chunk: " .. kind)
    print("###")
    print(chunk)
    print("###")

    local compiled, message = load(chunk, "derive-eq_record", "t")
    assert(compiled, message)
    local eq_fn = compiled()
    t.__eq = eq_fn
  end,
  enum = function(t, info)
    local name = info.name
    local variants = info.variants

    local variants_checks = {}
    for n, vname in ipairs(variants) do
      local vkind = name .. "_" .. vname
      local vdata = variants[vname]
      local vtype = vdata.type
      local vinfo = vdata.info
      local all_checks
      if vtype == "record" then
        local checks = {}
        for i, param in ipairs(vinfo.params) do
            checks[i] = string.format("left[%q] == right[%q]", param, param)
        end
        all_checks = table.concat(checks, " and ")
      elseif vtype == "unit" then
        all_checks = "true"
      else
        error("unknown variant type: " .. vtype)
      end
      local entry = string.format("[%q] = function(left, right) return %s end", vkind, all_checks)
      variants_checks[n] = entry
    end
    local all_variants_checks = "{\n  " .. table.concat(variants_checks, ",\n  ") .. "\n}"
    local define_all_variants_checks = "local all_variants_checks = " .. all_variants_checks

    local kind_check_expression = "left.kind == right.kind"
    local variant_check_expression = "all_variants_checks[left.kind](left, right)"
    local check_expression = kind_check_expression .. " and " .. variant_check_expression
    local check_function = "function(left, right) return " .. check_expression .. " end"
    local chunk = define_all_variants_checks .. "\nreturn " .. check_function

    print("derive eq: enum chunk: " .. name)
    print("###")
    print(chunk)
    print("###")

    local compiled, message = load(chunk, "derive-eq_enum", "t")
    assert(compiled, message)
    local eq_fn = compiled()
    t.__eq = eq_fn
  end,
}

local is = {
  enum = function(t, info)
    local idx = t.__index or {}
    t.__index = idx
    local name = info.name
    local variants = info.variants

    for n, vname in ipairs(variants) do
      local vkind = name .. "_" .. vname
      local chunk = string.format("return function(self) return self.kind == %q end", vkind)

      print("derive is: enum chunk: " .. vkind)
      print("###")
      print(chunk)
      print("###")

      local compiled, message = load(chunk, "derive-is_enum", "t")
      assert(compiled, message)
      idx["is_" .. vname] = compiled()
    end
  end,
}

local unwrap = {
  record = function(t, info)
    local idx = t.__index or {}
    t.__index = idx
    local kind = info.kind
    local params = info.params

    local returns = {}
    for i, param in ipairs(params) do
      returns[i] = string.format("self[%q]", param)
    end
    local all_returns = table.concat(returns, ", ")
    local chunk = "return function(self) return " .. all_returns .. " end"

    print("derive unwrap: record chunk: " .. kind)
    print("###")
    print(chunk)
    print("###")

    local compiled, message = load(chunk, "derive-unwrap_record", "t")
    assert(compiled, message)
    idx["unwrap_" .. kind] = compiled()
  end,
  enum = function(t, info)
    t:derive(is)
    local idx = t.__index
    local name = info.name
    local variants = info.variants

    for n, vname in ipairs(variants) do
      local vkind = name .. "_" .. vname
      local vdata = variants[vname]
      local vtype = vdata.type
      local vinfo = vdata.info
      local all_returns
      if vtype == "record" then
        local returns = {}
        for i, param in ipairs(vinfo.params) do
          returns[i] = string.format("self[%q]", param)
        end
        all_returns = table.concat(returns, ", ")
      elseif vtype == "unit" then
        all_returns = ""
      else
        error("unknown variant type: " .. vtype)
      end
      local error_message = "unwrap failed: unwrapping for a " .. vkind .. " but found a "
      local error_statement = string.format("error(%q .. self.kind)", error_message)
      local chunk = "return function(self) if self:is_" .. vname .. "() then return " .. all_returns .. " else " .. error_statement .. " end end"

      print("derive unwrap: enum chunk: " .. vkind)
      print("###")
      print(chunk)
      print("###")

      local compiled, message = load(chunk, "derive-unwrap_enum", "t")
      assert(compiled, message)
      idx["unwrap_" .. vname] = compiled()
    end
  end,
}

local as = {
  enum = function(t, info)
    t:derive(unwrap)
    local idx = t.__index
    local name = info.name
    local variants = info.variants

    for n, vname in ipairs(variants) do
      local vkind = name .. "_" .. vname
      local chunk = "return function(self) return pcall(function() return self:unwrap_" .. vname .. "() end) end"

      print("derive as: enum chunk: " .. vkind)
      print("###")
      print(chunk)
      print("###")

      local compiled, message = load(chunk, "derive-as_enum", "t")
      assert(compiled, message)
      idx["as_" .. vname] = compiled()
    end
  end,
}


  -- local typed = terms.inferrable_term.typed(terms.value.number_type, gen.declare_array(gen.builtin_number)(), terms.typed_term.literal(terms.value.number(1)))
  -- p(typed)
  -- p(getmetatable(typed))
  -- p(terms.inferrable_term == getmetatable(typed))

return {
  eq = eq,
  is = is,
  unwrap = unwrap,
  as = as,
}
