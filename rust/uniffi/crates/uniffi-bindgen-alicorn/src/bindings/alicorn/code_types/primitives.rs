// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use super::CodeType;
use uniffi_bindgen::interface;

trait IntoResult<T, E> {
    fn into_result(self) -> Result<T, E>;
}

impl<T, E> IntoResult<T, E> for Result<T, E> {
    #[inline(always)]
    fn into_result(self) -> Result<T, E> {
        self
    }
}

impl<T, E> IntoResult<T, E> for T {
    #[inline(always)]
    fn into_result(self) -> Result<T, E> {
        Ok(self)
    }
}

macro_rules! impl_code_type_for_primitive {
    ($T:ident, $type_label:literal, $canonical_name:literal, $($literal:tt)*) => {
        impl_code_type_for_primitive!(@normalize(@main()) $T, $type_label, $canonical_name, $($literal)*);
    };
    (@main() $T:ident, $type_label:literal, $canonical_name:literal, $($literal:tt)*) => {
        #[derive(Debug)]
        pub struct $T;

        impl $T {
            impl_code_type_for_primitive!(@fun(render) $T, $type_label, $canonical_name, $($literal)*);
        }

        impl CodeType for $T {
            fn type_label(&self) -> std::string::String {
                $type_label.into()
            }

            fn canonical_name(&self) -> std::string::String {
                $canonical_name.into()
            }

            impl_code_type_for_primitive!(@fun(literal) $T, $type_label, $canonical_name, $($literal)*);
        }

        impl TryFrom<interface::Type> for $T {
            type Error = anyhow::Error;

            fn try_from(value: interface::Type) -> Result<Self, Self::Error> {
                Ok(match value {
                    interface::Type::$T => Self,
                    _ => anyhow::bail!(concat!("Expected Type::", stringify!($T))),
                })
            }
        }
    };
    (@fun(render) $T:ident, $type_label:literal, $canonical_name:literal, ($($arg:tt)*) $pat:pat => Some($expr:expr)) => {
        pub fn render($($arg)*) -> std::string::String {
            $expr
        }
    };
    (@fun(render) $T:ident, $type_label:literal, $canonical_name:literal, ($($arg:tt)*) $pat:pat => None) => {
    };
    (@fun(render) $T:ident, $type_label:literal, $canonical_name:literal, ($($arg:tt)*) $pat:pat => $expr:expr) => {
        pub fn render($($arg)*) -> anyhow::Result<std::string::String> {
            Ok(match $expr {
                Some(rendered) => rendered,
                None => anyhow::bail!("Invalid literal {:?}", stringify!($T)),
            })
        }
    };
    (@fun(literal) $T:ident, $type_label:literal, $canonical_name:literal, ($($arg:tt: $arg_ty:ty),*) _ => $expr:expr) => {
        fn literal(&self, literal: &interface::Literal) -> anyhow::Result<std::string::String> {
            #[allow(unused_variables)]
            let rendered = match literal {
                _ => $expr,
            };
            Ok(match rendered {
                Some(rendered) => rendered,
                None => anyhow::bail!("Invalid literal {literal:?}"),
            })
        }
    };
    (@fun(literal) $T:ident, $type_label:literal, $canonical_name:literal, ($($arg:ident: $arg_ty:ty),*) $pat:pat => $expr:expr) => {
        fn literal(&self, literal: &interface::Literal) -> anyhow::Result<std::string::String> {
            match literal {
                $pat => IntoResult::into_result($T::render($($arg),*)),
                #[allow(unreachable_patterns)]
                _ => anyhow::bail!("Invalid literal {literal:?}"),
            }
        }
    };
    (@normalize $pack:tt $T:ident, $type_label:literal, $canonical_name:literal, (_: $i:ty) Int) => { impl_code_type_for_primitive!(
        @normalize $pack $T, $type_label, $canonical_name,
        (i: i64, radix: interface::Radix) &interface::Literal::Int(i, radix, interface::Type::$T) => Some(match radix {
            interface::Radix::Octal => format!("int(0o{i:o})"),
            interface::Radix::Decimal => format!("{i}"),
            interface::Radix::Hexadecimal => format!("{i:#x}"),
        })
    ); };
    (@normalize $pack:tt $T:ident, $type_label:literal, $canonical_name:literal, (_: $u:ty) UInt) => { impl_code_type_for_primitive!(
        @normalize $pack $T, $type_label, $canonical_name,
        (i: u64, radix: interface::Radix) &interface::Literal::UInt(i, radix, interface::Type::$T) => Some(match radix {
            interface::Radix::Octal => format!("0o{i:o}"),
            interface::Radix::Decimal => format!("{i}"),
            interface::Radix::Hexadecimal => format!("{i:#x}"),
        })
    ); };
    (@normalize $pack:tt $T:ident, $type_label:literal, $canonical_name:literal, (_: $f:ty) Float) => { impl_code_type_for_primitive!(
        @normalize $pack $T, $type_label, $canonical_name,
        (string: &str) interface::Literal::Float(string, interface::Type::$T) => Some(string.to_owned())
    ); };
    (@normalize($($pack:tt)*) $T:ident, $type_label:literal, $canonical_name:literal, $($literal:tt)*) => {
        impl_code_type_for_primitive!($($pack)* $T, $type_label, $canonical_name, $($literal)*);
    };
}

impl_code_type_for_primitive!(Boolean, "host-bool", "bool", (v: bool) &interface::Literal::Boolean(v) => Some(match v {
    true => "host-true",
    false => "host-false",
}.into()));
impl_code_type_for_primitive!(String, "host-string", "string", (s: &str) interface::Literal::String(s) => Some(format!("\"{s}\"")));
impl_code_type_for_primitive!(Bytes, "ffi-bytes", "bytes", (_: &[u8]) _ => None);
impl_code_type_for_primitive!(Int8, "ffi-i8", "i8", (_: i8) Int);
impl_code_type_for_primitive!(Int16, "ffi-i16", "i16", (_: i16) Int);
impl_code_type_for_primitive!(Int32, "ffi-i32", "i32", (_: i32) Int);
impl_code_type_for_primitive!(Int64, "ffi-i64", "i64", (_: i64) Int);
impl_code_type_for_primitive!(UInt8, "ffi-u8", "u8", (_: u8) UInt);
impl_code_type_for_primitive!(UInt16, "ffi-u16", "u16", (_: u16) UInt);
impl_code_type_for_primitive!(UInt32, "ffi-u32", "u32", (_: u32) UInt);
impl_code_type_for_primitive!(UInt64, "ffi-u64", "u64", (_: u64) UInt);
impl_code_type_for_primitive!(Float32, "ffi-f32", "f32", (_: f32) Float);
impl_code_type_for_primitive!(Float64, "ffi-f64", "f64", (_: f64) Float);
