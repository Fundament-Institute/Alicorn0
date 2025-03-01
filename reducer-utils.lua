-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

---@generic V, E
---@param data unknown
---@param val V
---@param env E
---@return true, { val: V, env: E }
local function accept_with_env(data, val, env)
	return true, { val = val, env = env }
end

---@generic V, E
---@param val_and_env { val: V, env: E }
---@return V, E
local function unpack_val_env(val_and_env)
	return val_and_env.val, val_and_env.env
end

---@module "_meta/reducer-utils/accept_bundled"
---@diagnostic disable-next-line: no-unknown, unused-local
local function accept_bundled(data, ...)
	return true, table.pack(...)
end

---@module "_meta/reducer-utils/unpack_bundle"
local function unpack_bundle(bun)
	return table.unpack(bun, 1, bun.n)
end

return {
	accept_with_env = accept_with_env,
	unpack_val_env = unpack_val_env,
	accept_bundled = accept_bundled,
	unpack_bundle = unpack_bundle,
}
