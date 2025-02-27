fn main() {
    if let Err(e) = uniffi_alicorn::uniffi_bindgen_main() {
        eprintln!("{e:?}");
        std::process::exit(1);
    }
}
