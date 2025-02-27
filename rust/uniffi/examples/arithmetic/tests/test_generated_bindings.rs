// SPDX-License-Identifier: MPL-2.0

uniffi::build_foreign_language_testcases!(
    "tests/bindings/test_arithmetic.rb",
    "tests/bindings/test_arithmetic.py",
    "tests/bindings/test_arithmetic.kts",
    "tests/bindings/test_arithmetic.swift",
);
uniffi_alicorn::build_foreign_language_testcases!("tests/bindings/test_arithmetic.alc",);
