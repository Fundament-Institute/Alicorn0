local function accept_with_env(data, val, env)
	return true, { val = val, env = env }
end
local function unpack_val_env(val_and_env)
	return val_and_env.val, val_and_env.env
end
local function accept_bundled(data, ...)
	return true, table.pack(...)
end
local function unpack_bundle(bun)
	return table.unpack(bun, 1, bun.n)
end

return {
	accept_with_env = accept_with_env,
	unpack_val_env = unpack_val_env,
	accept_bundled = accept_bundled,
	unpack_bundle = unpack_bundle,
}
