use std::{ffi::c_void, ptr::null};

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
    pub fn new() -> Result<Self, mlua::Error> {
        let lua = unsafe { Lua::unsafe_new() };

        // Load C libraries we already linked
        unsafe {
            let _: mlua::Value =
                lua.load_from_function("lpeg", lua.create_c_function(luaopen_lpeg)?)?;
            let _: mlua::Value =
                lua.load_from_function("lfs", lua.create_c_function(luaopen_lfs)?)?;
        }

        lua.load(ALICORN).exec()?;
        lua.load(
            r#" 
metalanguage = require "metalanguage"
evaluator = require "evaluator"
format = require "format-adapter"
base_env = require "base-env"
terms = require "terms"
exprs = require "alicorn-expressions"
profile = require "profile"

function alc_parse_string(src)
  return format.read(src, "<string value>")
end

function alc_parse_file(filename)
  local f = io.open(filename)
  local s = format.read(f:read("a"), filename)
  f:close()
  return s
end

function alc_process(code)          
  local env = base_env.create()

  local shadowed, env = env:enter_block(terms.block_purity.effectful)

  local ok, expr, env = code:match(
    { exprs.block(metalanguage.accept_handler, exprs.ExpressionArgs.new(terms.expression_goal.infer, env)) },
    metalanguage.failure_handler,
    nil
  )
  if not ok then
    error("inference failed")
  end

  local env, bound_expr, purity = env:exit_block(expr, shadowed)
  return bound_expr
end

function alc_evaluate(bound_expr)
  local type, usages, term = evaluator.infer(bound_expr, terms.typechecking_context())

  local gen = require "terms-generators"
  local set = gen.declare_set
  local unique_id = gen.builtin_table
  evaluator.typechecker_state:flow(
    type,
    nil,
    terms.value.program_type(
      terms.value.effect_row(set(unique_id)(terms.TCState), terms.value.effect_empty),
      evaluator.typechecker_state:metavariable(terms.typechecking_context()):as_value()
    ),
    nil,
    "final flow check"
  )

  return evaluator.evaluate(term, terms.runtime_context())
end
        "#,
        )
        .exec()?;

        Ok(Self { lua })
    }

    pub fn parse(&self, source: impl AsRef<str>) -> Result<mlua::Value, mlua::Error> {
        let alc_parse_string: LuaFunction = self.lua.load("alc_parse_string").eval()?;

        alc_parse_string.call(source.as_ref())
    }
    pub fn parse_file(
        &self,
        path: impl AsRef<std::path::Path>,
    ) -> Result<mlua::Value, mlua::Error> {
        let alc_parse_file: LuaFunction = self.lua.load("alc_parse_file").eval()?;

        alc_parse_file.call(path.as_ref().as_os_str().to_string_lossy())
    }
    pub fn process<'a>(&'a self, parsed: mlua::Value<'a>) -> Result<mlua::Value, mlua::Error> {
        let alc_process: LuaFunction = self.lua.load("alc_process").eval()?;
        alc_process.call(parsed)
    }

    pub fn evaluate<'a>(&'a self, terms: mlua::Value<'a>) -> Result<mlua::Value, mlua::Error> {
        let alc_evaluate: LuaFunction = self.lua.load("alc_evaluate").eval()?;
        alc_evaluate.call(terms)
    }

    pub fn execute<'a>(&'a self, program: mlua::Value<'a>) -> Result<mlua::Value, mlua::Error> {
        let execute_program: LuaFunction = self.lua.load("execute_program").eval()?;
        execute_program.call(program)
    }
}

#[test]
fn test_runtest_file() {
    let alicorn = Alicorn::new().unwrap();
    let ast = alicorn.parse_file("testfile.alc").unwrap();
    let terms = alicorn.process(ast).unwrap();
    let program = alicorn.evaluate(terms).unwrap();
    let result = alicorn.execute(program).unwrap();
    println!("LUA RESULT: {:?}", result);
}
