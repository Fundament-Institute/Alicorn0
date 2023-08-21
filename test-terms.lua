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
  local free_mv_a = terms.value.free.metavariable(mv_a)
  p(mv_a, free_mv_a)

  local unified = free_mv_a:unify(terms.value.level_type)
  assert(unified == terms.value.level_type)
  assert(mv_a:get_value() == terms.value.level_type)
end

function test_unify_more_metavariables()
  local tcs = terms.typechecker_state()

  -- terms.value.free.metavariable(...)
  -- terms.value.free.axiom(...)
  -- VS
  -- terms.value.free(terms.free.metavariable(...))

  local mv_a = tcs:metavariable()
  local mv_b = tcs:metavariable()
  p('mv_a', mv_a)
  local free_mv_a = terms.value.free.metavariable(mv_a)
  local free_mv_b = terms.value.free.metavariable(mv_b)
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
  local status, err = pcall(function() level_type:unify(prim) end)
  assert(status == false)
  p(err)

  local tcs = terms.typechecker_state()
  local mv_a = tcs:metavariable()
  local mv_b = tcs:metavariable()
  local freemeta = terms.value.free.metavariable
  local free_a = freemeta(mv_a)
  local free_b = freemeta(mv_b)

  local level0 = terms.value.level(0)
  local arginfo = terms.value.arginfo(terms.value.quantity(terms.quantity.unrestricted), terms.value.visibility(terms.visibility.explicit))
  local resinfo = terms.resultinfo(terms.purity.pure)

  local pi_a = terms.value.pi(free_a, arginfo, level0, resinfo)
  local pi_b = terms.value.pi(level0, arginfo, free_b, resinfo)
  local unified = pi_a:unify(pi_b)
  p(unified)
  assert(unified.argtype == unified.resulttype)
  assert(unified.argtype == level0)
end


test_levels()
test_star()
test_metavariable_bind_to_other_mv()
test_unify()
test_unify_more_metavariables()
test_unify_2()
