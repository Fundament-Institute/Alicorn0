// SPDX-License-Identifier: MPL-2.0

fn main() {
    uniffi::generate_scaffolding("src/arithmetic.udl").unwrap();
    uniffi_alicorn::generate_alicorn_scaffolding("src/arithmetic.udl").unwrap();
    // let out_dir = std::path::PathBuf::from(std::env::var("OUT_DIR").expect("$OUT_DIR missing?!"));
    // let manifest_dir = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("$CARGO_MANIFEST_DIR missing?!"));
    // for f in &["arithmetic.uniffi.rs", "arithmetic.uniffi-alicorn.rs"] {
    //     std::fs::copy(out_dir.join(f), manifest_dir.join(f)).expect(&*format!("couldn't copy {}", f));
    // }
}
