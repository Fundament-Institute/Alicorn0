// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>
#![cfg_attr(feature = "nightly", feature(proc_macro_expand))]
#![warn(rust_2018_idioms, unused_qualifications)]

//! Macros for `uniffi`.

use proc_macro::TokenStream;
use quote::quote;
use syn::LitStr;

mod setup_alicorn_scaffolding;
mod test;
mod util;

/// A macro to build testcases for a component's generated bindings.
///
/// This macro provides some plumbing to write automated tests for the generated
/// foreign language bindings of a component. As a component author, you can write
/// script files in the target foreign language(s) that exercise you component API,
/// and then call this macro to produce a `cargo test` testcase from each one.
/// The generated code will execute your script file with appropriate configuration and
/// environment to let it load the component bindings, and will pass iff the script
/// exits successfully.
///
/// To use it, invoke the macro with the name of a fixture/example crate as the first argument,
/// then one or more file paths relative to the crate root directory. It will produce one `#[test]`
/// function per file, in a manner designed to play nicely with `cargo test` and its test filtering
/// options.
#[proc_macro]
pub fn build_foreign_language_testcases(tokens: TokenStream) -> TokenStream {
    test::build_foreign_language_testcases(tokens)
}

/// Top-level initialization macro
///
/// The optional namespace argument is only used by the scaffolding templates to pass in the
/// CI namespace.
#[proc_macro]
pub fn setup_alicorn_scaffolding(tokens: TokenStream) -> TokenStream {
    let namespace = match syn::parse_macro_input!(tokens as Option<LitStr>) {
        Some(lit_str) => lit_str.value(),
        None => match util::mod_path() {
            Ok(v) => v,
            Err(e) => return e.into_compile_error().into(),
        },
    };
    setup_alicorn_scaffolding::setup_alicorn_scaffolding(namespace)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

/// A helper macro to include generated component scaffolding.
///
/// This is a simple convenience macro to include the UniFFI component
/// scaffolding as built by `uniffi_build::generate_scaffolding`.
/// Use it like so:
///
/// ```rs
/// uniffi_alicorn_macros::include_alicorn_scaffolding!("my_component_name");
/// ```
///
/// This will expand to the appropriate `include!` invocation to include
/// the generated `my_component_name.uniffi-alicorn.rs` (which it assumes has
/// been successfully built by your crate's `build.rs` script).
#[proc_macro]
pub fn include_alicorn_scaffolding(udl_stem: TokenStream) -> TokenStream {
    let udl_stem = syn::parse_macro_input!(udl_stem as LitStr);
    if std::env::var("OUT_DIR").is_err() {
        quote! {
            compile_error!("This macro assumes the crate has a build.rs script, but $OUT_DIR is not present");
        }
    } else {
        quote! {
            include!(concat!(env!("OUT_DIR"), "/", #udl_stem, ".uniffi-alicorn.rs"));
        }
    }.into()
}
