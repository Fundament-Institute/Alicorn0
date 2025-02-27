// SPDX-License-Identifier: MPL-2.0

#[derive(Debug, thiserror::Error)]
pub enum ArithmeticError {
    #[error("Integer overflow on an operation with {a} and {b}")]
    IntegerOverflow { a: u64, b: u64 },
}

fn add(a: u64, b: u64) -> Result<u64> {
    a.checked_add(b)
        .ok_or(ArithmeticError::IntegerOverflow { a, b })
}

fn sub(a: u64, b: u64) -> Result<u64> {
    a.checked_sub(b)
        .ok_or(ArithmeticError::IntegerOverflow { a, b })
}

fn div(dividend: u64, divisor: u64) -> u64 {
    if divisor == 0 {
        panic!("Can't divide by zero");
    }
    dividend / divisor
}

fn equal(a: u64, b: u64) -> bool {
    a == b
}

type Result<T, E = ArithmeticError> = std::result::Result<T, E>;

// (lazy) function to get _the_ `Alicorn` instance

uniffi::include_scaffolding!("arithmetic");
uniffi_alicorn::include_alicorn_scaffolding!("arithmetic");
// sets up function i call later; i can maybe even pass name. gets passed private struct?

// uniffi alicorn code is function that takes struct of user side and returns rust side for further
// use

// uniffi alicorn scaffolding sticks a Lua module early on via mlua into `package.loaded` that has
// all the host functions (`mlua::Lua::create_function`)

// Alicorn module/block returns a `record-of` with a bunch of host functions; those are typed so
// things are fine

// generated Alicorn module is exposed to Rust via `fn(alicorn: &Alicorn) -> mlua::String`
// returning format text
