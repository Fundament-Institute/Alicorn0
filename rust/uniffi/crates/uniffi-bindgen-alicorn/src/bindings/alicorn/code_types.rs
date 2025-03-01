// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use super::gen::CodeOracle;
use std::fmt::Debug;
use uniffi_bindgen::interface;

mod callback_interface;
mod compounds;
mod custom;
mod enum_;
mod miscellany;
mod object;
mod primitives;
mod record;

#[allow(unused_imports)]
pub use {
    callback_interface::CallbackInterface,
    compounds::{Map, Optional, Sequence},
    custom::Custom,
    enum_::{Enum, Variant},
    miscellany::{Duration, Timestamp},
    object::Object,
    primitives::{
        Boolean, Bytes, Float32, Float64, Int16, Int32, Int64, Int8, String, UInt16, UInt32,
        UInt64, UInt8,
    },
    record::Record,
};

/// A trait tor the implementation.
pub(super) trait CodeType: Debug {
    /// The language specific label used to reference this type. This will be used in
    /// method signatures and property declarations.
    fn type_label(&self) -> std::string::String {
        unimplemented!("Unimplemented for {}", std::any::type_name::<Self>())
    }

    /// A representation of this type label that can be used as part of another
    /// identifier. e.g. `read_foo()`, or `FooInternals`.
    ///
    /// This is especially useful when creating specialized objects or methods to deal
    /// with this type only.
    fn canonical_name(&self) -> std::string::String {
        self.type_label()
    }

    fn literal(&self, _literal: &interface::Literal) -> anyhow::Result<std::string::String> {
        unimplemented!("Unimplemented for {}", self.type_label())
    }

    /// Name of the FfiConverter
    ///
    /// This is the object that contains the lower, write, lift, and read methods for this type.
    fn ffi_converter_name(&self) -> std::string::String {
        format!("ffi-converter-{}", self.canonical_name())
    }

    /// Function to run at startup
    fn initialization_fn(&self) -> Option<std::string::String> {
        None
    }
}

pub(super) trait AsCodeType {
    fn as_code_type(&self) -> Box<dyn CodeType>;
}

impl<T: interface::AsType> AsCodeType for T {
    fn as_code_type(&self) -> Box<dyn CodeType> {
        use interface::Type;

        fn box_from_type<U: TryFrom<Type>>(value: Type) -> Box<U> {
            Box::new(U::try_from(value).unwrap_or_else(|_| unreachable!()))
        }

        // Map `Type` instances to a `Box<dyn CodeType>` for that type.
        //
        // There is a companion match in `templates/Types.alc` which performs a similar function for the
        // template code.
        //
        //   - When adding additional types here, make sure to also add a match arm to the `Types.alc` template.
        //   - To keep things manageable, let's try to limit ourselves to these 2 mega-matches
        let t = self.as_type();
        match t {
            Type::UInt8 => box_from_type::<UInt8>(t),
            Type::Int8 => box_from_type::<Int8>(t),
            Type::UInt16 => box_from_type::<UInt16>(t),
            Type::Int16 => box_from_type::<Int16>(t),
            Type::UInt32 => box_from_type::<UInt32>(t),
            Type::Int32 => box_from_type::<Int32>(t),
            Type::UInt64 => box_from_type::<UInt64>(t),
            Type::Int64 => box_from_type::<Int64>(t),
            Type::Float32 => box_from_type::<Float32>(t),
            Type::Float64 => box_from_type::<Float64>(t),
            Type::Boolean => box_from_type::<Boolean>(t),
            Type::String => box_from_type::<String>(t),
            Type::Bytes => box_from_type::<Bytes>(t),

            Type::Timestamp => box_from_type::<Timestamp>(t),
            Type::Duration => box_from_type::<Duration>(t),

            Type::Enum { .. } => box_from_type::<Enum>(t),
            Type::Object { .. } => box_from_type::<Object>(t),
            Type::Record { .. } => box_from_type::<Record>(t),
            Type::CallbackInterface { .. } => box_from_type::<CallbackInterface>(t),
            Type::Optional { .. } => box_from_type::<Optional>(t),
            Type::Sequence { .. } => box_from_type::<Sequence>(t),
            Type::Map { .. } => box_from_type::<Map>(t),
            Type::Custom { .. } => box_from_type::<Custom>(t),
        }
    }
}
