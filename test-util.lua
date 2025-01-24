local U = require "alicorn-utils"

local blah = {}
U.append(blah, "not 1")
U.append(blah, "2")
local blah2 = U.shadowarray(blah)
U.append(blah2, "3")
blah2[1] = "1"

--local endTime = os.time() + 3
--while os.time() < endTime do
--end

for k, v in ipairs(blah2) do
	if tostring(k) ~= v then
		error("FAIL: " .. tostring(k) .. " , " .. tostring(v))
	end
end

local blah3 = U.shadowarray(blah2)
U.append(blah3, "4")
blah3[5] = "5"
U.append(blah3, "6")

for k, v in ipairs(blah3) do
	if tostring(k) ~= v then
		error("FAIL: " .. tostring(k) .. " , " .. tostring(v))
	end
end

local blah4 = U.shadowarray(blah3)
if blah4[6] ~= "6" then
	error("FAIL blah4[6]: " .. tostring(blah4[6]))
end
if U.pop(blah4) ~= "6" then
	error("FAIL blah4")
end

if blah4[6] ~= nil then
	error("FAIL remove blah4[6]: " .. tostring(blah4[6]))
end
if blah3[6] ~= "6" then
	error("FAIL shadow blah3[6]: " .. tostring(blah3[6]))
end

U.commit(blah4)

if blah3[6] ~= nil then
	error("FAIL commit blah3[6]: " .. tostring(blah3[6]))
end

for k, v in ipairs(blah3) do
	if tostring(k) ~= v then
		error("FAIL: " .. tostring(k) .. " , " .. tostring(v))
	end
end

if blah2[5] ~= nil then
	error("FAIL blah2[5]: " .. tostring(blah2[5]))
end
U.commit(blah3)
if blah2[5] ~= "5" then
	error("FAIL commit blah2[5]: " .. tostring(blah2[5]))
end
if blah[5] ~= nil then
	error("FAIL blah[5]: " .. tostring(blah[5]))
end
U.commit(blah2)
if blah[5] ~= "5" then
	error("FAIL commit blah[5]: " .. tostring(blah[5]))
end

local bar = { foo = 1 }
if bar.foo ~= 1 then
	error("fail bar.foo: " .. tostring(bar.foo))
end

local foobar = U.shadowtable(bar)
foobar.bar = 2
if foobar.foo ~= 1 then
	error("fail foobar.foo: " .. tostring(foobar.foo))
end
if foobar.bar ~= 2 then
	error("fail foobar.bar: " .. tostring(foobar.bar))
end
foobar.foo = 3
if foobar.foo ~= 3 then
	error("fail foobar.foo: " .. tostring(foobar.foo))
end
if bar.foo ~= 1 then
	error("fail bar.foo: " .. tostring(bar.foo))
end

do
	local found = {}
	for k, v in pairs(foobar) do
		found[k] = v
	end

	if found.foo ~= 3 then
		error("fail found.foo: " .. tostring(foobar.foo))
	end
	if found.bar ~= 2 then
		error("fail found.foo: " .. tostring(bar.foo))
	end
end

do
	local store = nil
	local extractors = {
		---@return integer
		---@param obj RightCallEdge
		function(obj)
			return obj.left
		end,
		---@return integer
		---@param obj RightCallEdge
		function(obj)
			return obj.right
		end,
	}

	store = U.insert_tree_node({ left = "l1", right = "r1" }, store, 1, extractors, 0)
	store = U.insert_tree_node({ left = "l2", right = "r2" }, store, 1, extractors, 0)

	U.lock_table(store)
	U.unlock_table(store)
	store = U.insert_tree_node({ left = "l3", right = "r3" }, store, 1, extractors, 0)

	if store["l3"]["r3"] == nil then
		error("fail")
	end

	store = U.insert_tree_node({ left = "l4", right = "r4" }, store, 1, extractors, 1)

	if store["l3"]["r3"] == nil then
		error("fail")
	end

	store = U.insert_tree_node({ left = "l5", right = "r5" }, store, 1, extractors, 2)
	store = U.revert_tree_node(store, 2)
	if store["l5"] ~= nil then
		error("fail")
	end
	if store["l3"]["r3"] == nil then
		error("fail")
	end
	store = U.revert_tree_node(store, 2)
	if store["l4"] == nil then
		error("fail")
	end
	if store["l4"]["r4"] == nil then
		error("fail")
	end
	store = U.revert_tree_node(store, 1)
	if store["l4"] ~= nil then
		error("fail")
	end
	if store["l3"]["r3"] == nil then
		error("fail")
	end
	store = U.insert_tree_node({ left = "l4", right = "r4" }, store, 1, extractors, 1)
	store = U.insert_tree_node({ left = "l5", right = "r5" }, store, 1, extractors, 2)
	store = U.revert_tree_node(store, 2)
	if store["l3"]["r3"] == nil then
		error("fail")
	end

	U.lock_table(store)
	U.unlock_table(store)

	store = U.insert_tree_node({ left = "l6", right = "r6" }, store, 1, extractors, 2)

	if store["l3"]["r3"] == nil then
		error("fail")
	end

	if store["l4"] == nil then
		error("fail")
	end
	if store["l4"]["r4"] == nil then
		error("fail")
	end
	if store["l5"] ~= nil then
		error("fail")
	end
	if store["l6"] == nil then
		error("fail")
	end
	store = U.revert_tree_node(store, 2)
	if store["l6"] ~= nil then
		error("fail")
	end
	store = U.revert_tree_node(store, 1)
	if store["l4"] ~= nil then
		error("fail")
	end
	store = U.insert_tree_node({ left = "l3", right = "r3new" }, store, 1, extractors, 1)
	if store["l3"]["r3new"] == nil then
		error("fail")
	end
	if store["l3"]["r3"] == nil then
		error("fail")
	end
	store = U.revert_tree_node(store, 1)
	if store["l3"]["r3new"] ~= nil then
		error("fail")
	end
	if store["l3"]["r3"] == nil then
		error("fail")
	end
	store = U.insert_tree_node({ left = "l3", right = "r3new" }, store, 1, extractors, 1)
	store = U.commit_tree_node(store, 1)
	if store["l3"]["r3new"] == nil then
		error("fail")
	end
	if store["l3"]["r3"] == nil then
		error("fail")
	end
	store = U.insert_tree_node({ left = "l4", right = "r4" }, store, 1, extractors, 1)
	store = U.insert_tree_node({ left = "l5", right = "r5" }, store, 1, extractors, 2)

	if store["l4"] == nil then
		error("fail")
	end
	if store["l4"]["r4"] == nil then
		error("fail")
	end
	if store["l5"] == nil then
		error("fail")
	end
	if store["l5"]["r5"] == nil then
		error("fail")
	end

	store = U.commit_tree_node(store, 2)
	store = U.commit_tree_node(store, 1)
	if store["l4"] == nil then
		error("fail")
	end
	if store["l4"]["r4"] == nil then
		error("fail")
	end
	if store["l5"] == nil then
		error("fail")
	end
	if store["l5"]["r5"] == nil then
		error("fail")
	end

	store = U.insert_tree_node({ left = "l6", right = "r6" }, store, 1, extractors, 1)
	store = U.insert_tree_node({ left = "l7", right = "r7" }, store, 1, extractors, 2)

	if store["l6"] == nil then
		error("fail")
	end
	if store["l6"]["r6"] == nil then
		error("fail")
	end
	if store["l7"] == nil then
		error("fail")
	end
	if store["l7"]["r7"] == nil then
		error("fail")
	end
	store = U.revert_tree_node(store, 2)
	store = U.commit_tree_node(store, 1)

	if store["l6"] == nil then
		error("fail")
	end
	if store["l6"]["r6"] == nil then
		error("fail")
	end
	if store["l7"] ~= nil then
		error("fail")
	end
	--U.commit_tree_node(store, 1)

	local newstore = U.insert_tree_node({ left = "l1", right = "r1" }, nil, 1, extractors, 2)
	newstore = U.shadowtable(newstore)
	newstore = U.shadowtable(newstore)
	newstore = U.insert_tree_node({ left = "l6", right = "r6" }, newstore, 1, extractors, U.getshadowdepth(newstore))
	newstore = U.revert_tree_node(newstore, 1)
	newstore = U.insert_tree_node({ left = "l6", right = "r6" }, newstore, 1, extractors, U.getshadowdepth(newstore))

	local newstore = U.insert_tree_node({ left = "l1", right = "r1" }, nil, 1, extractors, 0)
	local newstore = U.insert_tree_node({ left = "l1", right = "r2" }, newstore, 1, extractors, 2)

	--local endTime = os.time() + 3
	--while os.time() < endTime do
	--end

	if newstore["l1"]["r1"] == nil then
		error("fail")
	end
	if newstore["l1"]["r2"] == nil then
		error("fail")
	end
	newstore = U.commit_tree_node(newstore, 2)

	if newstore["l1"]["r1"] == nil then
		error("fail")
	end
	if newstore["l1"]["r2"] == nil then
		error("fail")
	end

	local newstore = U.insert_tree_node({ left = "l2", right = "r1" }, newstore, 1, extractors, 3)

	if newstore["l2"]["r1"] == nil then
		error("fail")
	end

	local newstore = U.insert_tree_node({ left = "l2", right = "r2" }, newstore, 1, extractors, 5)
	local newstore = U.insert_tree_node({ left = "l3", right = "r2" }, newstore, 1, extractors, 5)

	if newstore["l2"]["r1"] == nil then
		error("fail")
	end
	if newstore["l2"]["r2"] == nil then
		error("fail")
	end

	newstore = U.commit_tree_node(newstore, 5)
	newstore = U.revert_tree_node(newstore, 4)

	if newstore["l2"]["r1"] == nil then
		error("fail")
	end
	if newstore["l2"]["r2"] ~= nil then
		error("fail")
	end
	if newstore["l3"] ~= nil then
		error("fail")
	end

	local newstore = U.insert_tree_node({ left = "l2", right = "r2" }, newstore, 1, extractors, 5)
	local newstore = U.insert_tree_node({ left = "l3", right = "r2" }, newstore, 1, extractors, 5)

	if newstore["l2"]["r1"] == nil then
		error("fail")
	end
	if newstore["l2"]["r2"] == nil then
		error("fail")
	end
	if newstore["l3"] == nil then
		error("fail")
	end

	newstore = U.revert_tree_node(newstore, 5)
	newstore = U.commit_tree_node(newstore, 4)

	if newstore["l2"]["r1"] == nil then
		error("fail")
	end
	if newstore["l2"]["r2"] ~= nil then
		error("fail")
	end
	if newstore["l3"] ~= nil then
		error("fail")
	end

	newstore = U.commit_tree_node(newstore, 3)
	newstore = U.revert_tree_node(newstore, 2)

	if newstore["l2"] ~= nil then
		error("fail")
	end
	if newstore["l2"] ~= nil then
		error("fail")
	end

	newstore = U.revert_tree_node(newstore, 2)

	if newstore["l1"]["r1"] == nil then
		error("fail")
	end
	if newstore["l1"]["r2"] == nil then
		error("fail")
	end

	newstore = U.revert_tree_node(newstore, 1)

	if newstore["l1"]["r1"] == nil then
		error("fail")
	end
	if newstore["l1"]["r2"] ~= nil then
		error("fail")
	end
end

--[[
local foo = metavariable()
speculate(function()
	local bar = something()
	flow(foo, bar)
	speculate(function()
		local quux = something_else()
		flow(quux, foo)
	end)
	fail()
end)
]]
print("Success!")
