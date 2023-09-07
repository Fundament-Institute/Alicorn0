-- persistent binary compacting buffer
-- for brevity, referred to as a fibonacci buffer.
-- in the case where the only methods implemented are append and get,
-- the two names are synonymous

local FibonacciBuffer = {}

local FibonacciBuffer_mt = {
  __index = FibonacciBuffer,
}

local function new()
  local fib_buf = {n = 0}
  setmetatable(fib_buf, FibonacciBuffer_mt)
  return fib_buf
end

function FibonacciBuffer:append(value)
  local n = self.n
  local n_partitions = #self
  -- scan through self to find how many partitions need to be merged.
  -- doing it this way means we don't build intermediate tables that
  -- don't get used in the output, especially during large merges.
  -- assuming we're still a binary compacting buffer, lengths are always powers of 2
  local merge_from = n_partitions
  local merge_length = 1
  for i = n_partitions - 1, 1, -1 do
    local partition_length = #self[i]
    if partition_length == merge_length then
      merge_from = merge_from - 1
      merge_length = merge_length * 2
    else
      break
    end
  end
  -- build the merged partition for the output
  local merged_partition = nil
  if merge_from == n_partitions then
    -- merging a single partition is a no-op
    -- just reference the old partition
    merged_partition = self[n_partitions]
  else
    merged_partition = {}
    local merged_length = 0
    for i = merge_from, n_partitions do
      local partition_length = #self[i]
      table.move(self[i], 1, partition_length, merged_length + 1, merged_partition)
      merged_length = merged_length + partition_length
    end
  end
  -- now we build the output
  local fib_buf = new()
  -- reference old partitions that didn't need to be merged
  table.move(self, 1, merge_from - 1, 1, fib_buf)
  fib_buf[merge_from] = merged_partition
  fib_buf[merge_from + 1] = { value }
  fib_buf.n = n + 1
  return fib_buf
end

-- one-based!!!
function FibonacciBuffer:get(index)
  for _, p in ipairs(self) do
    local length = #p
    if index <= length then
      return p[index]
    else
      index = index - length
    end
  end
  return nil
end

function FibonacciBuffer:len()
  return self.n
end

function FibonacciBuffer:debug_repr()
  local partition_strings = {}
  for i, p in ipairs(self) do
    partition_strings[i] = string.format("[ partition=%u table=\"%s\" length=%u data={ %s } ]", i, tostring(p), #p, table.concat(p, " "))
  end
  local output = string.format("table=\"%s\" n_partitions=%u %s", tostring(self), #self, table.concat(partition_strings, " "))
  return output
end

return new
