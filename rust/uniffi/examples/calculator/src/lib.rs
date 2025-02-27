// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use alicorn::Alicorn;
use std::any::Any;
use std::sync::OnceLock;
use std::any::TypeId;
use std::sync::Arc;

pub trait Calculator: Send + Sync {
    fn add_digit(&self, digit: u8);
    fn backspace(&self);
    fn apply_op(&self);
    fn set_op(&self, op: CalcOp);
    fn get(&self) -> f64;
    fn toggle_decimal(&self);
    fn copy(&self) -> Arc<dyn Calculator>;
    fn eq(&self, rhs: Arc<dyn Calculator>) -> bool;
}

impl dyn Calculator {
    #[inline]
    pub fn is<T: Any>(&self) -> bool {
        // Get `TypeId` of the type this function is instantiated with.
        let t = TypeId::of::<T>();

        // Get `TypeId` of the type in the trait object (`self`).
        let concrete = self.type_id();

        // Compare both `TypeId`s on equality.
        t == concrete
    }

    #[inline]
    pub unsafe fn downcast_ref_unchecked<T: Any>(&self) -> &T {
        debug_assert!(self.is::<T>());
        // SAFETY: caller guarantees that T is the correct type
        unsafe { &*(self as *const dyn Calculator as *const T) }
    }

    #[inline]
    pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
        if self.is::<T>() {
            // SAFETY: just checked whether we are pointing to the correct type, and we can rely on
            // that check for memory safety because we have implemented Any for all types; no other
            // impls can exist as they would conflict with our impl.
            unsafe { Some(self.downcast_ref_unchecked()) }
        } else {
            None
        }
    }
}

// Doesn't include instant actions that take no argument, like clear, backspace, pi, square, root, etc.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub enum CalcOp {
    #[default]
    None,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Square,
    Sqrt,
    Inv,
    Negate,
    Clear,
}

static CALCULATOR: OnceLock<Arc<dyn Calculator>> = OnceLock::new();

pub fn register(calc: Arc<dyn Calculator>) -> bool {
    if let Err(_) = CALCULATOR.set(calc) {
        return false;
    }
    let mlua = mlua::Lua::new();
    let alicorn = alicorn::Alicorn::new(Some(mlua)).expect("no alicorn :(");
    let format_text = uniffi_alicorn_calc_setup(&alicorn);
    alicorn.include(format_text.expect("no format :("), "uniffi-alicorn-calc").expect("no include :(");
    println!("Hello world!");
    true
}

pub fn get_registered() -> Arc<(dyn Calculator + 'static)> {
    CALCULATOR.get().expect("Calculator not yet registered").clone()
}

uniffi::include_scaffolding!("calculator");

uniffi_alicorn::include_alicorn_scaffolding!("calculator");
// sets up function i call later; i can maybe even pass name. gets passed private struct?

// uniffi alicorn code is function that takes struct of user side and returns rust side for further
// use

// uniffi alicorn scaffolding sticks a Lua module early on via mlua into `package.loaded` that has
// all the host functions (`mlua::Lua::create_function`)

// Alicorn module/block returns a `record-of` with a bunch of host functions; those are typed so
// things are fine

// generated Alicorn module is exposed to Rust via `fn(alicorn: &Alicorn) -> mlua::String`
// returning format text
