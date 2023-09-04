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

return eq
