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

test_levels()
test_star()
