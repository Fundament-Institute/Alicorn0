// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use mlua::prelude::*;

const ALICORN: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/alicorn.lua"));

extern "C-unwind" {
    fn luaopen_lpeg(L: *mut mlua::lua_State) -> std::ffi::c_int;
    fn luaopen_lfs(L: *mut mlua::lua_State) -> std::ffi::c_int;
}

pub struct Alicorn {
    lua: Lua,
}

impl Alicorn {
    pub fn new(unsafe_lua: Option<Lua>) -> Result<Self, mlua::Error> {
        let lua = unsafe_lua.unwrap_or_else(|| unsafe { Lua::unsafe_new() });

        // Load C libraries we already linked into our rust binary using our build script. This works because we can
        // declare the C functions directly and have the linker resolve them during the link step.
        unsafe {
            let _: mlua::Value =
                lua.load_from_function("lpeg", lua.create_c_function(luaopen_lpeg)?)?;
            let _: mlua::Value =
                lua.load_from_function("lfs", lua.create_c_function(luaopen_lfs)?)?;
        }

        lua.load(
            r#"
jit.opt.start("maxtrace=10000")
jit.opt.start("maxmcode=4096")
jit.opt.start("recunroll=5")
jit.opt.start("loopunroll=60")
        "#,
        )
        .exec()?;

        // Here, we load all the embedded alicorn source into the lua engine and execute it.
        lua.load(ALICORN).exec()?;

        // Then we create helper functions for compiling an alicorn source file that we can bind to mlua.
        lua.load(
            r#" 
metalanguage = require "metalanguage"
evaluator = require "evaluator"
format = require "format-adapter"
formatter = require "format"
base_env = require "base-env"
terms = require "terms"
exprs = require "alicorn-expressions"
profile = require "profile"
util = require "alicorn-utils"
env = base_env.create()

function alc_parse_string(src, name)
  return format.read(src, name or "<string value>")
end

function alc_parse_file(filename)
  local f = io.open(filename)
  if not f then
    error("Couldn't find " .. filename)
  end

  local s = format.read(f:read("a"), filename)
  f:close()
  return s
end

function alc_process(code)
  local shadowed, inner_env = env:enter_block(terms.block_purity.effectful)

	local ok, expr, inner_env = code:match({
		exprs.top_level_block(
			metalanguage.accept_handler,
			{ exprargs = exprs.ExpressionArgs.new(terms.expression_goal.infer, inner_env), name = name }
		),
	}, metalanguage.failure_handler, nil)

  if not ok then
    print(tostring(expr))
    error("processing failed (error printed to stdout)")
  end

  local outer_env, bound_expr, purity = inner_env:exit_block(expr, shadowed)
  env = outer_env
  return bound_expr
end

function alc_evaluate(bound_expr)
  local ok, type, usages, term = evaluator.infer(bound_expr, terms.typechecking_context())

  if not ok then
    print(tostring(type))
    error("inference failed (error printed to stdout)")
	end
  
  local gen = require "terms-generators"
  local set = gen.declare_set
  local unique_id = gen.builtin_table
  local ok, err = evaluator.typechecker_state:flow(
			type,
			env.typechecking_context,
			terms.flex_value.program_type(
				terms.flex_value.effect_row(terms.unique_id_set(terms.TCState, terms.lua_prog)),
				evaluator.typechecker_state:metavariable(env.typechecking_context):as_flex()
			),
			env.typechecking_context,
			terms.constraintcause.primitive("final flow check", formatter.anchor_here())
		)
    
  if not ok then
    print(err)
    error("evaluation failed (error printed to stdout)")
  end

  return evaluator.evaluate(term, env.typechecking_context.runtime_context, env.typechecking_context)
end

function alc_execute(program)
  local result_exec = evaluator.execute_program(program)
  --print("result_exec: (value term follows)")
  --print(result_exec)
  return result_exec:unwrap_host_tuple_value():unpack()
end
        "#,
        )
        .exec()?;

        Ok(Self { lua })
    }

    pub fn parse(&self, source: impl AsRef<str>, name: Option<impl AsRef<str>>) -> Result<mlua::Value, mlua::Error> {
        let alc_parse_string: LuaFunction = self.lua.load("alc_parse_string").eval()?;

        alc_parse_string.call((source.as_ref(), name.as_ref().map(|s| s.as_ref())))
    }
    pub fn parse_file(
        &self,
        path: impl AsRef<std::path::Path>,
    ) -> Result<mlua::Value, mlua::Error> {
        let alc_parse_file: LuaFunction = self.lua.load("alc_parse_file").eval()?;

        alc_parse_file.call(path.as_ref().as_os_str().to_string_lossy())
    }
    pub fn process<'a>(&'a self, parsed: mlua::Value<'a>) -> Result<mlua::Value<'a>, mlua::Error> {
        let alc_process: LuaFunction = self.lua.load("alc_process").eval()?;
        alc_process.call(parsed)
    }

    pub fn evaluate<'a>(&'a self, terms: mlua::Value<'a>) -> Result<mlua::Value<'a>, mlua::Error> {
        let alc_evaluate: LuaFunction = self.lua.load("alc_evaluate").eval()?;
        alc_evaluate.call(terms)
    }

    pub fn execute<'a, R: FromLuaMulti<'a>>(
        &'a self,
        program: mlua::Value<'a>,
    ) -> Result<R, mlua::Error> {
        let execute_program: LuaFunction = self.lua.load("alc_execute").eval()?;
        execute_program.call(program)
    }
}

#[test]
fn test_runtest_file() {
    // set the working directory to some random temporary folder to sabotage loading any of the files from this crate, as a crate including this one wouldn't have access to those files
    let old = std::env::current_dir().unwrap();
    let temp_dir = std::env::temp_dir();
    let root = std::path::Path::new(&temp_dir);
    std::env::set_current_dir(&root).unwrap();

    let alicorn = Alicorn::new(None).unwrap();

    // Restore working dir so we can find prelude.alc
    std::env::set_current_dir(&old).unwrap();
    let ast = alicorn.parse_file("prelude.alc").unwrap();
    let terms = alicorn.process(ast).unwrap();
    let program = alicorn.evaluate(terms).unwrap();
    let result: LuaValue<'_> = alicorn.execute(program).unwrap();
    println!("LUA RESULT: {:?}", result);
}
