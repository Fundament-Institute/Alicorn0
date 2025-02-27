// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

//! # Uniffi: easily build cross-platform software components in Rust
//!
//! This is an Alicorn backend for [UniFFI](mod@uniffi).

#![warn(rust_2018_idioms, unused_qualifications)]

use anyhow::{anyhow, bail, Context, Result};
use camino::{Utf8Path, Utf8PathBuf};
use fs_err::{self as fs, File};
use serde::Deserialize;
use std::{
    io::{ErrorKind, Write},
    process::Command,
};
use uniffi_bindgen::interface::ComponentInterface;

pub mod bindings;
pub mod scaffolding;

// Generate the infrastructural Rust code for implementing the UDL interface,
// such as the `extern "C"` function definitions and record data types.
// Locates and parses Cargo.toml to determine the name of the crate.
pub fn generate_component_alicorn_scaffolding(
    udl_file: &Utf8Path,
    out_dir_override: Option<&Utf8Path>,
    format_code: bool,
) -> Result<()> {
    let component = parse_udl(udl_file, &crate_name_from_cargo_toml(udl_file)?)
        .with_context(|| format!("parsing udl file {udl_file}"))?;
    generate_component_alicorn_scaffolding_inner(component, udl_file, out_dir_override, format_code)
}

// Generate the infrastructural Rust code for implementing the UDL interface,
// such as the `extern "C"` function definitions and record data types, using
// the specified crate name.
pub fn generate_component_alicorn_scaffolding_for_crate(
    udl_file: &Utf8Path,
    crate_name: &str,
    out_dir_override: Option<&Utf8Path>,
    format_code: bool,
) -> Result<()> {
    let component =
        parse_udl(udl_file, crate_name).with_context(|| format!("parsing udl file {udl_file}"))?;
    generate_component_alicorn_scaffolding_inner(component, udl_file, out_dir_override, format_code)
}

fn generate_component_alicorn_scaffolding_inner(
    component: ComponentInterface,
    udl_file: &Utf8Path,
    out_dir_override: Option<&Utf8Path>,
    format_code: bool,
) -> Result<()> {
    let file_stem = udl_file.file_stem().context("not a file")?;
    let filename = format!("{file_stem}.uniffi-alicorn.rs");
    let out_path = get_out_dir(udl_file, out_dir_override)?.join(filename);
    let mut f = File::create(&out_path)?;
    write!(
        f,
        "{}",
        scaffolding::RustAlicornScaffolding::new(&component, file_stem)
    )
    .context("Failed to write output file")?;
    if format_code {
        format_code_with_rustfmt(&out_path).context("formatting generated Rust code")?;
    }
    Ok(())
}

// Given the path to a UDL file, locate and parse the corresponding Cargo.toml to determine
// the library crate name.
// Note that this is largely a copy of code in uniffi_macros/src/util.rs, but sharing it
// isn't trivial and it's not particularly complicated so we've just copied it.
fn crate_name_from_cargo_toml(udl_file: &Utf8Path) -> Result<String> {
    #[derive(Deserialize)]
    struct CargoToml {
        package: Package,
        #[serde(default)]
        lib: Lib,
    }

    #[derive(Deserialize)]
    struct Package {
        name: String,
    }

    #[derive(Default, Deserialize)]
    struct Lib {
        name: Option<String>,
    }

    let file = uniffi_bindgen::guess_crate_root(udl_file)?.join("Cargo.toml");
    let cargo_toml_bytes =
        fs::read(file).context("Can't find Cargo.toml to determine the crate name")?;

    let cargo_toml = toml::from_slice::<CargoToml>(&cargo_toml_bytes)?;

    let lib_crate_name = cargo_toml
        .lib
        .name
        .unwrap_or_else(|| cargo_toml.package.name.replace('-', "_"));

    Ok(lib_crate_name)
}

fn get_out_dir(udl_file: &Utf8Path, out_dir_override: Option<&Utf8Path>) -> Result<Utf8PathBuf> {
    Ok(match out_dir_override {
        Some(s) => {
            // Create the directory if it doesn't exist yet.
            fs::create_dir_all(s)?;
            s.canonicalize_utf8().context("Unable to find out-dir")?
        }
        None => udl_file
            .parent()
            .context("File has no parent directory")?
            .to_owned(),
    })
}

fn parse_udl(udl_file: &Utf8Path, crate_name: &str) -> Result<ComponentInterface> {
    let udl = fs::read_to_string(udl_file)
        .with_context(|| format!("Failed to read UDL from {udl_file}"))?;
    let group = uniffi_udl::parse_udl(&udl, crate_name)?;
    ComponentInterface::from_metadata(group)
}

fn format_code_with_rustfmt(path: &Utf8Path) -> Result<()> {
    let status = Command::new("rustfmt").arg(path).status().map_err(|e| {
        let ctx = match e.kind() {
            ErrorKind::NotFound => "formatting was requested, but rustfmt was not found",
            _ => "unknown error when calling rustfmt",
        };
        anyhow!(e).context(ctx)
    })?;
    if !status.success() {
        bail!("rustmt failed when formatting scaffolding. Note: --no-format can be used to skip formatting");
    }
    Ok(())
}

// FIXME(HACK):
// Include the rinja config file into the build.
// That way cargo tracks the file and other tools relying on file tracking see it as well.
// See https://bugzilla.mozilla.org/show_bug.cgi?id=1774585
// In the future rinja should handle that itself by using the `track_path::path` API,
// see https://github.com/rust-lang/rust/pull/84029
#[allow(dead_code)]
mod __unused {
    const _: &[u8] = include_bytes!("../rinja.toml");
}
