// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

fn main() {
    if let Err(e) = uniffi_alicorn::uniffi_bindgen_main() {
        eprintln!("{e:?}");
        std::process::exit(1);
    }
}
