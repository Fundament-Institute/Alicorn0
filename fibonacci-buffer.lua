-- persistent binary compacting buffer
-- for brevity, referred to as a fibonacci buffer.
-- in the case where the only methods implemented are append and get,
-- the two names are synonymous

---@class (exact) FibonacciPartition
---@field n integer
---@field [integer] any

---@class (exact) FibonacciBuffer
---@field n integer
---@field [integer] FibonacciPartition
local FibonacciBuffer = {}
local FibonacciBuffer_mt = {}

---@return FibonacciBuffer
local function new()
	return setmetatable({ n = 0 }, FibonacciBuffer_mt)
end

---@param value any
---@return FibonacciBuffer
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
		local partition_length = self[i].n
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
			local partition_length = self[i].n
			table.move(self[i], 1, partition_length, merged_length + 1, merged_partition)
			merged_length = merged_length + partition_length
		end
		merged_partition.n = merged_length
	end
	-- now we build the output
	local fib_buf = new()
	-- reference old partitions that didn't need to be merged
	table.move(self, 1, merge_from - 1, 1, fib_buf)
	fib_buf[merge_from] = merged_partition
	fib_buf[merge_from + 1] = { value, n = 1 }
	fib_buf.n = n + 1
	return fib_buf
end

-- one-based!!!
---@generic T
---@param index integer
---@return T
function FibonacciBuffer:get(index)
	for _, p in ipairs(self) do
		local length = p.n
		if index <= length then
			return p[index]
		else
			index = index - length
		end
	end
	return nil
end

---@generic T
---@param index integer
---@param value T
---@return FibonacciBuffer
function FibonacciBuffer:set(index, value)
	if index < 1 then
		error("fibonacci buffer set() index out of bounds")
	end
	local n = self.n
	for i, p in ipairs(self) do
		local length = p.n
		if index <= length then
			-- build new output based on self
			local fib_buf = new()
			table.move(self, 1, n, 1, fib_buf)
			fib_buf.n = n
			-- recreate partition which is changing
			local newp = {}
			table.move(p, 1, length, 1, newp)
			newp.n = length
			-- now set
			newp[index] = value
			fib_buf[i] = newp
			return fib_buf
		else
			index = index - length
		end
	end
	error("fibonacci buffer set() index out of bounds")
end

---@return integer
function FibonacciBuffer:len()
	return self.n
end

---@param other FibonacciBuffer
---@return boolean
function FibonacciBuffer:eq(other)
	local other_mt = getmetatable(other)
	if other_mt ~= FibonacciBuffer_mt then
		return false
	end
	local n, other_n = self.n, other.n
	if n ~= other_n then
		return false
	end
	-- same length means same number of partitions
	local n_partitions = #self
	local cur = 0
	-- compare physical equality of partitions first for efficiency
	for i = 1, n_partitions do
		if self[i] == other[i] then
			cur = cur + self[i].n
		else
			break
		end
	end
	-- then, if needed, handle the rest through structural equality
	for i = cur + 1, n do
		if self:get(i) ~= other:get(i) then
			return false
		end
	end
	return true
end

---@return string
function FibonacciBuffer:debug_repr()
	local partition_strings = {}
	for i, p in ipairs(self) do
		partition_strings[i] = string.format(
			'[ partition=%u table="%s" length=%u data={ %s } ]',
			i,
			tostring(p),
			p.n,
			table.concat(p, " ", 1, p.n)
		)
	end
	local output =
		string.format('table="%s" n_partitions=%u %s', tostring(self), #self, table.concat(partition_strings, " "))
	return output
end

FibonacciBuffer_mt.__index = FibonacciBuffer
FibonacciBuffer_mt.__eq = FibonacciBuffer.eq

return new
