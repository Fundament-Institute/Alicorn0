// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use mlua::{
    prelude::*,
    Either::{self, Left, Right},
};

const ALICORN: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/alicorn.lua"));
const PRELUDE: &[u8] = include_bytes!("prelude.alc");
const GLSL_PRELUDE: &[u8] = include_bytes!("glsl-prelude.alc");

extern "C-unwind" {
    fn luaopen_lpeg(L: *mut mlua::lua_State) -> std::ffi::c_int;
    fn luaopen_lfs(L: *mut mlua::lua_State) -> std::ffi::c_int;
}

pub struct Alicorn {
    lua: Lua,
    runner: AlicornRunner,
}

pub struct AlicornRunner {
    runner: LuaTable,
}

#[repr(transparent)]
struct LuaResult<T, E>(pub Result<T, E>);
impl<T, E> From<LuaResult<T, E>> for Result<T, E> {
    #[inline(always)]
    fn from(value: LuaResult<T, E>) -> Self {
        value.0
    }
}
impl<T: FromLuaMulti, E: FromLuaMulti> FromLuaMulti for LuaResult<T, E> {
    fn from_lua_multi(mut values: LuaMultiValue, lua: &Lua) -> mlua::Result<Self> {
        let ok = values
            .pop_front()
            .map(|value| bool::from_lua(value, lua))
            .unwrap_or(Ok(false))?;
        if ok {
            T::from_lua_multi(values, lua).map(|value| LuaResult(Ok(value)))
        } else {
            E::from_lua_multi(values, lua).map(|value| LuaResult(Err(value)))
        }
    }
}

macro_rules! trivial_lua_value {
    ($t:path) => {
        impl FromLua for $t {
            fn from_lua(value: LuaValue, lua: &Lua) -> mlua::Result<Self> {
                LuaValue::from_lua(value, lua).map(Self)
            }
        }
        impl IntoLua for $t {
            fn into_lua(self, lua: &Lua) -> mlua::Result<LuaValue> {
                self.0.into_lua(lua)
            }
        }
    };
}

#[repr(transparent)]
pub struct ConstructedSyntax(pub mlua::Value);
trivial_lua_value!(ConstructedSyntax);

#[repr(transparent)]
pub struct FlexValue(pub mlua::Value);
trivial_lua_value!(FlexValue);

#[repr(transparent)]
pub struct TypedTerm(pub mlua::Value);
trivial_lua_value!(TypedTerm);

#[repr(transparent)]
pub struct AnchoredInferrableTerm(pub mlua::Value);
trivial_lua_value!(AnchoredInferrableTerm);

/// `terms.purity`
///
/// TODO: proper Lua value conversion
#[repr(transparent)]
pub struct Purity(pub mlua::Value);
trivial_lua_value!(Purity);

/// `terms.block_purity`
pub enum BlockPurity {
    /// `terms.block_purity.effectful`
    Effectful,
    /// `terms.block_purity.pure`
    Pure,
    /// `terms.block_purity.dependent`
    Dependent {
        /// `flex_value`
        val: FlexValue,
    },
    /// `terms.block_purity.inherit`
    Inherit,
}
impl IntoLua for BlockPurity {
    fn into_lua(self, lua: &Lua) -> mlua::Result<LuaValue> {
        let block_purity = lua
            .load(r#"require("terms").block_purity"#)
            .eval::<LuaTable>()?;
        match self {
            Self::Effectful => block_purity.get("effectful"),
            Self::Pure => block_purity.get("pure"),
            Self::Dependent { val } => block_purity.get::<LuaFunction>("dependent")?.call(val),
            Self::Inherit => block_purity.get("inherit"),
        }
    }
}
impl FromLua for BlockPurity {
    fn from_lua(value: LuaValue, lua: &Lua) -> mlua::Result<Self> {
        let block_purity = lua
            .load(r#"require("terms").block_purity"#)
            .eval::<LuaTable>()?;
        if block_purity
            .get::<LuaFunction>("value_check")?
            .call(&value)?
        {
            let value = LuaTable::from_lua(value, lua)?;
            if let Ok(()) = value
                .get::<LuaFunction>("as_effectful")?
                .call::<LuaResult<_, ()>>(&value)?
                .into()
            {
                Ok(Self::Effectful)
            } else if let Ok(()) = value
                .get::<LuaFunction>("as_pure")?
                .call::<LuaResult<_, ()>>(&value)?
                .into()
            {
                Ok(Self::Pure)
            } else if let Ok(val) = value
                .get::<LuaFunction>("as_dependent")?
                .call::<LuaResult<_, ()>>(&value)?
                .into()
            {
                Ok(Self::Dependent { val })
            } else if let Ok(()) = value
                .get::<LuaFunction>("as_inherit")?
                .call::<LuaResult<_, ()>>(value)?
                .into()
            {
                Ok(Self::Inherit)
            } else {
                unreachable!()
            }
        } else {
            Err(mlua::Error::FromLuaConversionError {
                from: value.type_name(),
                to: "terms.block_purity".to_owned(),
                message: Some("expected terms.block_purity".to_owned()),
            })
        }
    }
}

impl AlicornRunner {
    pub fn enter_block(&self, purity: BlockPurity) -> Result<(), mlua::Error> {
        self.runner
            .get::<LuaFunction>("enter_block")?
            .call((&self.runner, purity))
    }
    pub fn exit_block(
        &self,
        expr: AnchoredInferrableTerm,
    ) -> Result<(AnchoredInferrableTerm, Purity), mlua::Error> {
        self.runner
            .get::<LuaFunction>("exit_block")?
            .call((&self.runner, expr))
    }
    pub fn read_format(
        &self,
        format_text: mlua::String,
        id: mlua::String,
    ) -> Result<ConstructedSyntax, mlua::Error> {
        self.runner
            .get::<LuaFunction>("read_format")?
            .call((&self.runner, format_text, id))
    }
    pub fn read_file(
        &self,
        format_file: Either<mlua::String, mlua::Value>,
        id: Option<mlua::String>,
    ) -> Result<ConstructedSyntax, mlua::Error> {
        self.runner
            .get::<LuaFunction>("read_file")?
            .call((&self.runner, format_file, id))
    }
    pub fn try_parse_syntax(
        &self,
        syntax: mlua::Table,
        id: mlua::String,
    ) -> Result<Result<AnchoredInferrableTerm, mlua::String>, mlua::Error> {
        Ok(self
            .runner
            .get::<LuaFunction>("try_parse_syntax")?
            .call::<LuaResult<_, _>>((&self.runner, syntax, id))?
            .into())
    }
    pub fn parse_syntax(
        &self,
        syntax: mlua::Table,
        id: mlua::String,
    ) -> Result<AnchoredInferrableTerm, mlua::Error> {
        self.runner
            .get::<LuaFunction>("parse_syntax")?
            .call((&self.runner, syntax, id))
    }
    pub fn try_parse_format(
        &self,
        format_text: mlua::String,
        id: mlua::String,
    ) -> Result<Result<AnchoredInferrableTerm, mlua::String>, mlua::Error> {
        Ok(self
            .runner
            .get::<LuaFunction>("try_parse_format")?
            .call::<LuaResult<_, _>>((&self.runner, format_text, id))?
            .into())
    }
    pub fn parse_format(
        &self,
        format_text: mlua::String,
        id: mlua::String,
    ) -> Result<AnchoredInferrableTerm, mlua::Error> {
        self.runner
            .get::<LuaFunction>("parse_format")?
            .call((&self.runner, format_text, id))
    }
    pub fn try_parse_file(
        &self,
        format_file: Either<mlua::String, (mlua::Value, mlua::String)>,
    ) -> Result<Result<AnchoredInferrableTerm, mlua::String>, mlua::Error> {
        Ok(self
            .runner
            .get::<LuaFunction>("try_parse_file")?
            .call::<LuaResult<_, _>>(match format_file {
                Left(path) => (&self.runner, Left(path), None),
                Right((file, id)) => (&self.runner, Right(file), Some(id)),
            })?
            .into())
    }
    pub fn parse_file(
        &self,
        format_file: Either<mlua::String, (mlua::Value, mlua::String)>,
    ) -> Result<AnchoredInferrableTerm, mlua::Error> {
        self.runner
            .get::<LuaFunction>("parse_file")?
            .call(match format_file {
                Left(path) => (&self.runner, Left(path), None),
                Right((file, id)) => (&self.runner, Right(file), Some(id)),
            })
    }
    pub fn try_infer_expr(
        &self,
        expr: AnchoredInferrableTerm,
    ) -> Result<Result<(FlexValue, mlua::Value, TypedTerm), mlua::String>, mlua::Error> {
        Ok(self
            .runner
            .get::<LuaFunction>("try_infer_expr")?
            .call::<LuaResult<_, _>>((&self.runner, expr))?
            .into())
    }
    pub fn infer_expr(
        &self,
        expr: AnchoredInferrableTerm,
    ) -> Result<(FlexValue, mlua::Value, TypedTerm), mlua::Error> {
        self.runner
            .get::<LuaFunction>("parse_file")?
            .call((&self.runner, expr))
    }
    pub fn try_typecheck_program_type(
        &self,
        r#type: FlexValue,
    ) -> Result<Result<(), mlua::String>, mlua::Error> {
        Ok(self
            .runner
            .get::<LuaFunction>("try_typecheck_program_type")?
            .call::<LuaResult<_, _>>((&self.runner, r#type))?
            .into())
    }
    pub fn typecheck_program_type(&self, r#type: FlexValue) -> Result<(), mlua::Error> {
        self.runner
            .get::<LuaFunction>("typecheck_program_type")?
            .call((&self.runner, r#type))
    }
    pub fn try_evaluate_term(
        &self,
        r#type: FlexValue,
    ) -> Result<Result<(), mlua::String>, mlua::Error> {
        Ok(self
            .runner
            .get::<LuaFunction>("try_evaluate_term")?
            .call::<LuaResult<_, _>>((&self.runner, r#type))?
            .into())
    }
    pub fn evaluate_term(&self, r#type: FlexValue) -> Result<(), mlua::Error> {
        self.runner
            .get::<LuaFunction>("evaluate_term")?
            .call((&self.runner, r#type))
    }
    pub fn try_evaluate_program_expr(
        &self,
        program_expr: AnchoredInferrableTerm,
    ) -> Result<Result<FlexValue, mlua::String>, mlua::Error> {
        Ok(self
            .runner
            .get::<LuaFunction>("try_evaluate_program_expr")?
            .call::<LuaResult<_, _>>((&self.runner, program_expr))?
            .into())
    }
    pub fn evaluate_program_expr(
        &self,
        program_expr: AnchoredInferrableTerm,
    ) -> Result<FlexValue, mlua::Error> {
        self.runner
            .get::<LuaFunction>("evaluate_program_expr")?
            .call((&self.runner, program_expr))
    }
    pub fn evaluate_program_format(
        &self,
        program_format_text: mlua::String,
        program_id: mlua::String,
    ) -> Result<FlexValue, mlua::Error> {
        self.runner
            .get::<LuaFunction>("evaluate_program_format")?
            .call((&self.runner, program_format_text, program_id))
    }
    pub fn evaluate_program_file(
        &self,
        program_format_file: Either<mlua::String, (mlua::Value, mlua::String)>,
    ) -> Result<FlexValue, mlua::Error> {
        self.runner
            .get::<LuaFunction>("evaluate_program_file")?
            .call(match program_format_file {
                Left(path) => (&self.runner, Left(path), None),
                Right((file, id)) => (&self.runner, Right(file), Some(id)),
            })
    }
    pub fn execute_program_value(
        &self,
        program_value: FlexValue,
    ) -> Result<LuaMultiValue, mlua::Error> {
        self.runner
            .get::<LuaFunction>("execute_program_value")?
            .call((&self.runner, program_value))
    }
    pub fn execute_program_format(
        &self,
        program_format_text: mlua::String,
        program_id: mlua::String,
    ) -> Result<LuaMultiValue, mlua::Error> {
        self.runner
            .get::<LuaFunction>("execute_program_format")?
            .call((&self.runner, program_format_text, program_id))
    }
    pub fn execute_program_file(
        &self,
        program_format_file: Either<mlua::String, (mlua::Value, mlua::String)>,
    ) -> Result<LuaMultiValue, mlua::Error> {
        self.runner
            .get::<LuaFunction>("execute_program_file")?
            .call(match program_format_file {
                Left(path) => (&self.runner, Left(path), None),
                Right((file, id)) => (&self.runner, Right(file), Some(id)),
            })
    }
}

impl Alicorn {
    pub fn new(lua: Option<Lua>) -> Result<Self, mlua::Error> {
        let lua = lua.unwrap_or_else(|| Lua::new());

        // Load C libraries we already linked into our rust binary using our build script. This works because we can
        // declare the C functions directly and have the linker resolve them during the link step.
        unsafe {
            let _: mlua::Value =
                lua.load_from_function("lpeg", lua.create_c_function(luaopen_lpeg)?)?;
            let _: mlua::Value =
                lua.load_from_function("lfs", lua.create_c_function(luaopen_lfs)?)?;
        }

        // Here, we load all the embedded alicorn source into the lua engine and execute it.
        lua.load(ALICORN).exec()?;

        // Then we create helper functions for compiling an alicorn source file that we can bind to mlua.
        let runner: LuaTable = lua
            .load(r#"alicorn_runner = require("alicorn-runner").Runner(); return alicorn_runner"#)
            .eval()?;

        let alicorn = Self {
            lua,
            runner: AlicornRunner { runner },
        };
        alicorn.runner.enter_block(BlockPurity::Effectful)?;

        _ = alicorn.include(PRELUDE, "prelude.alc")?;

        Ok(alicorn)
    }

    pub fn load_glsl_prelude(&self) -> Result<(), mlua::Error> {
        _ = self.include(GLSL_PRELUDE, "glsl-prelude.alc")?;

        Ok(())
    }

    pub fn include(
        &self,
        source: impl AsRef<[u8]>,
        name: impl AsRef<str>,
    ) -> Result<AnchoredInferrableTerm, mlua::Error> {
        self.runner.parse_format(
            self.lua.create_string(source.as_ref())?,
            self.lua.create_string(name.as_ref())?,
        )
    }

    pub fn include_file(
        &self,
        path: impl AsRef<std::path::Path>,
    ) -> Result<AnchoredInferrableTerm, mlua::Error> {
        self.runner
            .parse_file(Either::Left(self.lua.create_string(
                path.as_ref().as_os_str().to_string_lossy().as_bytes(),
            )?))
    }

    pub fn execute<R: FromLuaMulti>(
        &self,
        source: impl AsRef<[u8]>,
        name: impl AsRef<str>,
    ) -> Result<R, mlua::Error> {
        R::from_lua_multi(
            self.runner.execute_program_format(
                self.lua.create_string(source.as_ref())?,
                self.lua.create_string(name.as_ref())?,
            )?,
            &self.lua,
        )
    }

    pub fn execute_file<R: FromLuaMulti>(
        &self,
        path: impl AsRef<std::path::Path>,
    ) -> Result<R, mlua::Error> {
        R::from_lua_multi(
            self.runner.execute_program_file(Either::Left(
                self.lua
                    .create_string(path.as_ref().as_os_str().to_string_lossy().as_bytes())?,
            ))?,
            &self.lua,
        )
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
    let result: LuaValue = alicorn
        .execute(
            "host-tuple-of(tuple-desc-singleton(host-type, host-number))(4)",
            format!("{}:{}", file!(), line!() - 1),
        )
        .unwrap();
    assert_eq!(result, LuaValue::Integer(4));
}
