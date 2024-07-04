local U = require "./utils"

local blah = {}
U.append(blah, "not 1")
U.append(blah, "2")
local blah2 = U.shadowarray(blah)
U.append(blah2, "3")
blah2[1] = "1"

for k, v in ipairs(blah2) do
	if tostring(k) ~= v then
		error("FAIL: " .. tostring(k) .. " , " .. tostring(v))
	end
end

local blah3 = U.shadowarray(blah2)
U.append(blah3, "4")
blah3[5] = "5"

for k, v in ipairs(blah3) do
	if tostring(k) ~= v then
		error("FAIL: " .. tostring(k) .. " , " .. tostring(v))
	end
end

if blah2[5] ~= nil then
	error("FAIL blah2[5]" .. tostring(blah2[5]))
end
U.commit(blah3)
if blah2[5] ~= "5" then
	error("FAIL commit blah2[5]" .. tostring(blah2[5]))
end
if blah[5] ~= nil then
	error("FAIL blah[5]" .. tostring(blah[5]))
end
U.commit(blah2)
if blah[5] ~= "5" then
	error("FAIL commit blah[5]" .. tostring(blah[5]))
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

print("Success!")
