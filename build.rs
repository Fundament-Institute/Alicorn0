use std::str::FromStr;

use mlua::prelude::*;

const ALICORN_SOURCES: &[&str] = &[
    "libs/abstract-codegen.lua",
    "types/binding.lua",
    "types/block_purity.lua",
    "types/checkable.lua",
    "types/continuation.lua",
    "types/effect_id.lua",
    "types/expression_goal.lua",
    "types/free.lua",
    "types/inferrable.lua",
    "types/neutral_value.lua",
    "types/purity.lua",
    "types/result_info.lua",
    "types/typed.lua",
    "types/value.lua",
    "types/visibility.lua",
    "alicorn-expressions.lua",
    "alicorn-utils.lua",
    "backend-builder.lua",
    "base-env.lua",
    "core-operatives.lua",
    "cotuple.lua",
    "derivers.lua",
    "environment.lua",
    "evaluator.lua",
    "fibonacci-buffer.lua",
    "format-adapter.lua",
    "format.lua",
    "internals-interface.lua",
    "lazy-prefix-tree.lua",
    "metalanguage.lua",
    "modules.lua",
    "operative-scratch.lua",
    "pretty-printable-trait.lua",
    "pretty-printer.lua",
    "profile.lua",
    "reducer-utils.lua",
    "syntax-schema.lua",
    "terms-gen-meta.lua",
    "terms-generators.lua",
    "terms-pretty.lua",
    "terms.lua",
    "traits.lua",
    "typesystem.lua",
];

const DEST: &str = "alicorn.lua";

const LPEG_SOURCES: &[&str] = &[
    "lpcap.c",
    "lpcode.c",
    "lpcset.c",
    "lpprint.c",
    "lptree.c",
    "lpvm.c",
];

fn main() -> LuaResult<()> {
    let lua = Lua::new();

    let sources = lua.create_table_with_capacity(ALICORN_SOURCES.len(), 0)?;
    for i in 0..ALICORN_SOURCES.len() {
        sources.set(i + 1, ALICORN_SOURCES[i])?;
        println!("cargo:rerun-if-changed={}", ALICORN_SOURCES[i]);
    }

    lua.globals().set("sources", sources)?;
    lua.globals().set(
        "dest",
        std::path::PathBuf::from_str(
            &std::env::var_os("OUT_DIR")
                .expect("OUT_DIR not set in build script???")
                .to_string_lossy(),
        )
        .expect("Path was invalid UTF-8")
        .join(DEST)
        .to_str()
        .expect("Path was invalid UTF-8"),
    )?;

    lua.load(
        r#"
local data = {}
 
for i, name in ipairs( sources ) do
  local bc = string.dump( loadfile( package.searchpath( name, package.path ) ), true )
  table.insert( data, ( "package.preload[%q] = load( %q )\n" ) : format( name, bc ) )
end
    
local code = table.concat( data )
local file = io.open( dest, "wb" )
local bytecode = string.dump(load(code), true)
file:write( bytecode )
file:close()
    "#,
    )
    .exec()
    .unwrap();

    {
        cc::Build::new()
            .opt_level(2)
            .define("NDEBUG", None)
            .std("c11")
            .include("vendor/luajit2/src") // TODO: get this from mlua somehow?
            .flag("/GR-")
            .warnings(false)
            .files(LPEG_SOURCES.iter().map(|x| format!("vendor/lpeg/{}", x)))
            .compile("lpeg");

        println!("cargo:rustc-link-lib=lpeg");

        cc::Build::new()
            .opt_level(2)
            .define("NDEBUG", None)
            .std("c11")
            .include("vendor/luajit2/src") // TODO: get this from mlua somehow?
            .flag("/GR-")
            .warnings(false)
            .file("vendor/luafilesystem/src/lfs.c")
            .compile("lfs");

        println!("cargo:rustc-link-lib=lfs");

        // workaround for https://github.com/rust-lang/cc-rs/issues/594
        /*let out_dir = std::env::var("OUT_DIR").unwrap();
        let mut command = cc::Build::new()
            .opt_level(2)
            .define("NDEBUG", None)
            .std("c11")
            .include("vendor/luajit2/src") // TODO: get this from mlua somehow?
            .flag("/GR-")
            .get_compiler()
            .to_command();
        command.args(LPEG_SOURCES.iter().map(|x| format!("vendor/lpeg/{}", x)));
        command.arg(format!("/link /DYNAMICBASE /DLL /FORCE /OUT:{}/lpeg.dll", out_dir).as_str());
        let output = command
            .status()
            .expect("Failed to execute compiler command, do you have MSVC installed?");

        //if output.stderr
        //panic!("{}", String::from_utf8(output.stderr).unwrap());

        #[cfg(not(target_os = "windows"))]
        builder
            .get_compiler()
            .to_command()
            .args(["-shared", "-fPIC", "-o"])
            .arg(format!(r#"/OUT:"{}""#, target).as_str())
            .args(&objects)
            .status()
            .unwrap();
          */
    }

    Ok(())
}
