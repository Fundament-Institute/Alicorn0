local terms = require './terms'

function test_levels()
  local test_term = terms.inferrable.level_max(terms.inferrable.level_suc(terms.inferrable.level0), terms.inferrable.level0)
  local inferred_type, inferred_term = terms.infer(test_term, {})
  p(inferred_type)
  assert(inferred_type.kind == "value_level_type")
  local result = terms.evaluate(inferred_term, {})
  p(result)
  assert(result.kind == "value_level")
  assert(result.level == 1)
end

function test_star()
  local test_term = terms.inferrable.star
  local inferred_type, inferred_term = terms.infer(test_term, {})
  p(inferred_type, inferred_term)
  assert(inferred_type.kind == "value_star")
  local result = terms.evaluate(inferred_term, {})
  p(result)
  assert(result.kind == "value_star")
  assert(result.level == 0)
end

function test_metavariable_bind_to_other_mv()
  local tcs = terms.typechecker_state()
  local mv_a = tcs:metavariable()
  local mv_b = tcs:metavariable()
  mv_a:bind_metavariable(mv_a) -- noop
  mv_b:bind_metavariable(mv_a) -- mv_b binds to mv_a
  local canonical_a = mv_a:get_canonical()
  local canonical_b = mv_b:get_canonical()
  p(mv_a, mv_b, canonical_a, canonical_b)
  assert(mv_b:get_canonical().id == mv_a.id)
  local mv_c = tcs:metavariable()
  mv_c:bind_metavariable(mv_b)
  assert(mv_c:get_canonical().id == mv_a.id)
  -- check that bound ID was correctly collapsed
  assert(tcs.mvs[mv_c.id].bound_mv_id == mv_a.id)
end

function test_unify()
  local tcs = terms.typechecker_state()

  local mv_a = tcs:metavariable()
  local free_mv_a = terms.value.neutral(terms.neutral_value.free.metavariable(mv_a))
  p(mv_a, free_mv_a)

  local unified = free_mv_a:unify(terms.value.level_type)
  assert(unified == terms.value.level_type)
  assert(mv_a:get_value() == terms.value.level_type)
end

function test_unify_more_metavariables()
  local tcs = terms.typechecker_state()

  -- terms.neutral_value.free.metavariable(...)
  -- terms.neutral_value.free.axiom(...)
  -- VS
  -- terms.neutral_value.free(terms.free.metavariable(...))

  local mv_a = tcs:metavariable()
  local mv_b = tcs:metavariable()
  p('mv_a', mv_a)
  local free_mv_a = terms.value.neutral(terms.neutral_value.free.metavariable(mv_a))
  local free_mv_b = terms.value.neutral(terms.neutral_value.free.metavariable(mv_b))
  p(mv_a, free_mv_a)

  free_mv_b:unify(free_mv_a)
  assert(mv_b:get_canonical().id == mv_a.id)

  local unified = free_mv_a:unify(terms.value.level_type)
  assert(unified == terms.value.level_type)
  assert(mv_a:get_value() == terms.value.level_type)

  assert(mv_b:get_value() == terms.value.level_type)
end

function test_unify_2()
  local level_type = terms.value.level_type
  local prim = terms.value.prim
  local success, err = pcall(function() level_type:unify(prim) end)
  assert(success == false)
  p(err)

  local tcs = terms.typechecker_state()
  local mv_a = tcs:metavariable()
  local mv_b = tcs:metavariable()
  local freemeta = function(mv) return terms.value.neutral(terms.neutral_value.free.metavariable(mv)) end
  local free_a = freemeta(mv_a)
  local free_b = freemeta(mv_b)

  local level0 = terms.value.level(0)
  local quantity = terms.value.quantity(terms.quantity.unrestricted)
  local qlevel0 = terms.value.qtype(quantity, level0)
  local visibility = terms.value.visibility(terms.visibility.explicit)
  local arginfo = terms.value.arginfo(visibility)
  local resinfo = terms.resultinfo(terms.purity.pure)

  local pi_a = terms.value.pi(free_a, arginfo, qlevel0, resinfo)
  local pi_b = terms.value.pi(qlevel0, arginfo, free_b, resinfo)
  local unified = pi_a:unify(pi_b)
  p(unified)
  assert(unified.argtype == unified.resulttype)
  assert(unified.argtype == qlevel0)

  local mv_c = tcs:metavariable()
  local free_c = freemeta(mv_c)
  local qlevel0_c = terms.value.qtype(free_c, level0)
  local pi_c = terms.value.pi(qlevel0_c, arginfo, qlevel0, resinfo)
  local unified_c = pi_c:unify(unified)
  p(unified_c)
  assert(unified_c.argtype.quantity == quantity)

  local quantity_2 = terms.value.quantity(terms.quantity.linear)
  local qlevel0_2 = terms.value.qtype(quantity_2, level0)
  local pi_2 = terms.value.pi(qlevel0_2, arginfo, qlevel0, resinfo)
  local success_2, err_2 = pcall(function() pi_2:unify(pi_c) end)
  assert(success_2 == false)
  p(err_2)
end


test_levels()
test_star()
test_metavariable_bind_to_other_mv()
test_unify()
test_unify_more_metavariables()
test_unify_2()
