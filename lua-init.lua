-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local M = {}

M.jit_enabled = true
M.lldebugger_enabled = os.getenv("LOCAL_LUA_DEBUGGER_VSCODE") == "1"
if M.lldebugger_enabled then
	M.jit_enabled = false
end

---@param jit_enabled boolean?
function M.set_jit(jit_enabled)
	if jit_enabled ~= nil then
		M.jit_enabled = jit_enabled
	end
	if jit then
		if M.jit_enabled then
			jit.opt.start("maxtrace=10000")
			jit.opt.start("maxmcode=4096")
			jit.opt.start("recunroll=5")
			jit.opt.start("loopunroll=60")
		else
			jit.off()
		end
	end
end

M.set_jit()

if M.lldebugger_enabled then
	require("lldebugger").start(true)
end

function M.debug_break()
	if M.lldebugger_enabled then
		require("lldebugger").requestBreak()
	end
end

return M
