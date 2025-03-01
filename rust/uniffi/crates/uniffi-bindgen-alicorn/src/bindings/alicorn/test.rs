// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use anyhow::{Context, Result};
use camino::Utf8Path;
use std::{env, ffi::OsString, process::Command};
use uniffi_bindgen::{
    bindings::RunScriptOptions, cargo_metadata::CrateConfigSupplier,
    library_mode::generate_bindings,
};
use uniffi_testing::UniFFITestHelper;

/// Run Alicorn tests for a UniFFI test fixture
pub fn run_test(tmp_dir: &str, fixture_name: &str, script_file: &str) -> Result<()> {
    run_script(
        tmp_dir,
        fixture_name,
        script_file,
        vec![],
        &RunScriptOptions::default(),
    )
}

/// Run a Alicorn script
///
/// This function will set things up so that the script can import the UniFFI bindings for a crate
pub fn run_script(
    tmp_dir: &str,
    crate_name: &str,
    script_file: &str,
    args: Vec<String>,
    _options: &RunScriptOptions,
) -> Result<()> {
    let script_path = Utf8Path::new(script_file).canonicalize_utf8()?;
    let test_helper = UniFFITestHelper::new(crate_name)?;
    let out_dir = test_helper.create_out_dir(tmp_dir, &script_path)?;
    let cdylib_path = test_helper.copy_cdylib_to_out_dir(&out_dir)?;
    generate_bindings(
        &cdylib_path,
        None,
        &super::BindingGenerator,
        &CrateConfigSupplier::from(test_helper.cargo_metadata()),
        None,
        &out_dir,
        false,
    )?;

    let pythonpath = env::var_os("PYTHONPATH").unwrap_or_else(|| OsString::from(""));
    let pythonpath = env::join_paths(
        env::split_paths(&pythonpath).chain(vec![out_dir.to_path_buf().into_std_path_buf()]),
    )?;

    let mut command = Command::new("python3");
    command
        .current_dir(out_dir)
        .env("PYTHONPATH", pythonpath)
        .arg(script_path)
        .args(args);
    let status = command
        .spawn()
        .context("Failed to spawn `python3` when running script")?
        .wait()
        .context("Failed to wait for `python3` when running script")?;
    if !status.success() {
        anyhow::bail!("running `python3` failed");
    }
    Ok(())
}
