// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

//! Generate foreign language bindings for a uniffi component.
//!
//! This module contains all the code for generating foreign language bindings,
//! along with some helpers for executing foreign language scripts or tests.

mod alicorn;
pub use alicorn::BindingGenerator as AlicornBindingGenerator;

#[cfg(feature = "bindgen-tests")]
pub use self::alicorn::test as alicorn_test;
