// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use std::str::FromStr;

use mlua::prelude::*;

const ALICORN_SOURCES: &[&str] = &[
    "./lua-init.lua",
    "libs/abstract-codegen.lua",
    "./alicorn-expressions.lua",
    "./alicorn-runner.lua",
    "./alicorn-utils.lua",
    "./base-env.lua",
    "./derivers.lua",
    "./environment.lua",
    "./evaluator-types.lua",
    "./evaluator.lua",
    "./fibonacci-buffer.lua",
    "./format-adapter.lua",
    "./format.lua",
    "./glsl-print.lua",
    "./internals-interface.lua",
    "./lazy-prefix-tree.lua",
    "./lua-ext.lua",
    "./metalanguage.lua",
    "./pretty-printer.lua",
    "./profile.lua",
    "./reducer-utils.lua",
    "./syntax-schema.lua",
    "./terms-gen-meta.lua",
    "./terms-generators.lua",
    "./terms-pretty.lua",
    "./terms.lua",
    "./traits.lua",
    "./unformatter.lua",
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

    let sources = lua.create_table_with_capacity(ALICORN_SOURCES.len() + 20, 0)?;
    let mut i = 0;
    while i < ALICORN_SOURCES.len() {
        sources.set(i + 1, ALICORN_SOURCES[i])?;
        println!("cargo:rerun-if-changed={}", ALICORN_SOURCES[i]);
        i += 1;
    }

    // Here, we use a lua script to automate ingesting all of the alicorn lua and merging it into a single huge
    // lua file inside OUT_DIR using the DEST constant variable name (which should be alicorn.lua). This is used
    // in our lib.rs when we are building the rust crate.
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

for i, path in ipairs( sources ) do
  local content, err = loadfile( path )
  if content == nil then
    error(err)
  end
  local codefile = io.open(path)
  local source = codefile:read("*a")
  codefile:close()
  local bc = string.dump( content, false )
  local name = string.match( path, ".+/(.+).lua" )
  table.insert( data, ( "package.preload[%q], err = load( %q, %q, 't' )\n if err ~= nil then error(err) end \n" ) : format( name, source, name ) )
end
    
local code = table.concat( data )
local file = io.open( dest, "wb" )
--local bytecode = string.dump(load(code), false)
--file:write( "print('inside alicorn')\n" )
file:write( code )
--file:write( "print('exited alicorn') \n print(package.preload['metalanguage'])" )
file:close()
    "#,
    )
    .exec()
    .unwrap();

    // Here we use rust's CC library to build lpeg and lfs lua libraries, then tell cargo to link the resulting libraries with our binary.
    {
        cc::Build::new()
            .opt_level(2)
            .define("NDEBUG", None)
            .std("c11")
            .include("vendor/luajit2/src") // TODO: get this from mlua somehow?
            .flag_if_supported("/GR-")
            .warnings(false)
            .files(LPEG_SOURCES.iter().map(|x| format!("vendor/lpeg/{}", x)))
            .compile("lpeg");

        println!("cargo:rustc-link-lib=lpeg");

        cc::Build::new()
            .opt_level(2)
            .define("NDEBUG", None)
            .std(if cfg!(target_os = "windows") {
                "c11"
            } else {
                "gnu11" // Fuck GCC
            })
            .include("vendor/luajit2/src") // TODO: get this from mlua somehow?
            .flag_if_supported("/GR-")
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
