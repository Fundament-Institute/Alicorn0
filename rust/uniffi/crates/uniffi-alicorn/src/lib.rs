// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

//! Reexports items from other UniFFI crates.

// pub use uniffi_core_alicorn::*;
pub use uniffi_macros_alicorn::{include_alicorn_scaffolding, setup_alicorn_scaffolding};
#[cfg(any(doc, feature = "cli"))]
mod cli;
// #[cfg(feature = "bindgen")]
// pub use uniffi_bindgen_alicorn::library_mode::generate_bindings as generate_bindings_library_mode;
#[cfg(feature = "bindgen-tests")]
pub use uniffi_bindgen_alicorn::bindings::alicorn_test;
#[cfg(feature = "bindgen")]
pub use uniffi_bindgen_alicorn::bindings::AlicornBindingGenerator;
#[cfg(feature = "build")]
pub use uniffi_build_alicorn::{
    generate_alicorn_scaffolding, generate_alicorn_scaffolding_for_crate,
};
#[cfg(feature = "bindgen-tests")]
pub use uniffi_macros_alicorn::build_foreign_language_testcases;

#[cfg(feature = "cli")]
pub use cli::*;
