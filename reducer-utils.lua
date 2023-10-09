local function accept_with_env(data, val, env)
	return true, { val = val, env = env }
end

return {
	accept_with_env = accept_with_env,
}
