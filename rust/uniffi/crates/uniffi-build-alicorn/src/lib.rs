// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use anyhow::Context;
use camino::Utf8Path;
use std::env;

/// Generate the rust "scaffolding" required to build a UniFFI component.
///
/// Given the path to an UDL file, this function will call the `uniffi-bindgen`
/// command-line tool to generate the `pub extern "C"` functions and other supporting
/// code required to expose the defined interface from Rust. The expectation is that
/// this will be called from a crate's build script, and the resulting file will
/// be `include!()`ed into the build.
///
/// This function will attempt to locate and parse a corresponding Cargo.toml to
/// determine the crate name which will host this UDL.
///
/// Given an UDL file named `example.udl`, the generated scaffolding will be written
/// into a file named `example.uniffi.rs` in the `$OUT_DIR` directory.
pub fn generate_alicorn_scaffolding(udl_file: impl AsRef<Utf8Path>) -> anyhow::Result<()> {
    let udl_file = udl_file.as_ref();
    println!("cargo:rerun-if-changed={udl_file}");
    println!("cargo:rerun-if-env-changed=UNIFFI_TESTS_DISABLE_EXTENSIONS");
    let out_dir = env::var("OUT_DIR").context("$OUT_DIR missing?!")?;
    uniffi_bindgen_alicorn::generate_component_alicorn_scaffolding(
        udl_file,
        Some(out_dir.as_ref()),
        false,
    )
}

/// Like generate_scaffolding, but uses the specified crate_name instead of locating and parsing
/// Cargo.toml.
pub fn generate_alicorn_scaffolding_for_crate(
    udl_file: impl AsRef<Utf8Path>,
    crate_name: &str,
) -> anyhow::Result<()> {
    let udl_file = udl_file.as_ref();

    println!("cargo:rerun-if-changed={udl_file}");
    // The UNIFFI_TESTS_DISABLE_EXTENSIONS variable disables some bindings, but it is evaluated
    // at *build* time, so we need to rebuild when it changes.
    println!("cargo:rerun-if-env-changed=UNIFFI_TESTS_DISABLE_EXTENSIONS");
    let out_dir = env::var("OUT_DIR").context("$OUT_DIR missing?!")?;
    uniffi_bindgen_alicorn::generate_component_alicorn_scaffolding_for_crate(
        udl_file,
        crate_name,
        Some(out_dir.as_ref()),
        false,
    )
}
