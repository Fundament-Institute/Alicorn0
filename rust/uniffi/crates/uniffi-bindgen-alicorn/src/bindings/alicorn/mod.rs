// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

//! # Alicorn bindings backend for UniFFI
//!
//! This module generates Alicorn bindings from a [`uniffi_bindgen::ComponentInterface`] definition,
//! using Alicorn's [`mlua`](https://crates.io/crates/mlua) embedding.

use anyhow::{anyhow, Context};
use camino::Utf8PathBuf;
use fs_err as fs;
use serde::{Deserialize, Serialize};
use uniffi_bindgen::{self as bindgen, BindingGenerator as _};

mod code_types;
mod gen;
#[cfg(feature = "bindgen-tests")]
pub mod test;

/// The Alicorn bindings generated from a [`crate::ComponentInterface`].
pub struct Bindings {
    pub library: String,
}

pub struct BindingGenerator;

/// Config options to customize the generated Alicorn.
///
/// Note that this can only be used to control details of the Alicorn *that do not affect the underlying component*,
/// since the details of the underlying component are entirely determined by the `ComponentInterface`.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BindingConfig {
    module_name: Option<String>,
}

impl uniffi_bindgen::BindingGenerator for BindingGenerator {
    type Config = BindingConfig;

    fn new_config(&self, root_toml: &toml::Value) -> anyhow::Result<Self::Config> {
        Ok(
            match root_toml.get("bindings").and_then(|b| b.get("alicorn")) {
                Some(v) => v.clone().try_into()?,
                None => Default::default(),
            },
        )
    }

    fn update_component_configs(
        &self,
        _settings: &uniffi_bindgen::GenerationSettings,
        components: &mut Vec<uniffi_bindgen::Component<Self::Config>>,
    ) -> anyhow::Result<()> {
        for c in &mut *components {
            c.config
                .module_name
                .get_or_insert_with(|| c.ci.namespace().into());
        }
        Ok(())
    }

    fn write_bindings(
        &self,
        settings: &uniffi_bindgen::GenerationSettings,
        components: &[uniffi_bindgen::Component<Self::Config>],
    ) -> anyhow::Result<()> {
        for uniffi_bindgen::Component { ci, config, .. } in components {
            let Bindings { library } = self.generate_bindings(config, &mut ci.clone())?;
            let library_file = settings.out_dir.join(format!("{}.alc", ci.namespace()));
            fs::write(&library_file, library)?;

            if settings.try_format_code {
                if let Err(e) = Err::<(), _>(anyhow!("Alicorn does not yet have an auto-formatter"))
                {
                    println!(
                        "Warning: Unable to auto-format {} using some formatter: {e:?}",
                        library_file.file_name().unwrap(),
                    )
                }
            }
        }

        Ok(())
    }
}

/// Generate Alicorn bindings
///
/// This is used by the uniffi-bindgen-alicorn command, which supports Alicorn-specific options.
///
/// In the future, we may want to replace the generalized `uniffi-bindgen` with a set of
/// specialized `uniffi-bindgen-[language]` commands.
pub fn generate_bindings(options: BindingOptions) -> anyhow::Result<()> {
    #[cfg(feature = "cargo-metadata")]
    let config_supplier = {
        use bindgen::cargo_metadata::CrateConfigSupplier;
        let mut cmd = cargo_metadata::MetadataCommand::new();
        if options.metadata_no_deps {
            cmd.no_deps();
        }
        let metadata = cmd.exec().context("error running cargo metadata")?;
        CrateConfigSupplier::from(metadata)
    };
    #[cfg(any(rust_analyzer, not(feature = "cargo-metadata")))]
    let config_supplier = bindgen::EmptyCrateConfigSupplier;

    fs::create_dir_all(&options.out_dir)?;

    let generator = BindingGenerator;

    let mut components =
        bindgen::library_mode::find_components(&options.library_path, &config_supplier)?
            // map the TOML configs into a our Config struct
            .into_iter()
            .map(|bindgen::Component { ci, config }| {
                let config = generator.new_config(&config.into())?;
                Ok(bindgen::Component { ci, config })
            })
            .collect::<anyhow::Result<Vec<_>>>()?;
    generator.update_component_configs(&bindgen::GenerationSettings::default(), &mut components)?;

    for bindgen::Component { ci, config } in &components {
        if options.generate_library {
            let source_file = options
                .out_dir
                .join(format!("{}.alicorn", config.module_name()));
            fs::write(
                &source_file,
                generator.generate_library(config, &mut ci.clone())?,
            )?;
        }
    }

    Ok(())
}

#[derive(Debug)]
pub struct BindingOptions {
    pub generate_library: bool,
    pub library_path: Utf8PathBuf,
    pub out_dir: Utf8PathBuf,
    pub module_name: Option<String>,
    pub metadata_no_deps: bool,
}
