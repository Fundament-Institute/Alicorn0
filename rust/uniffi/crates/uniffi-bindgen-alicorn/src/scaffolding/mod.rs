// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use anyhow::{anyhow, Result};
use heck::{ToShoutySnakeCase, ToKebabCase};
use rinja::{Error, Template};
use std::borrow::Borrow;
use uniffi_bindgen::interface::{AsType, ComponentInterface, Type};

#[derive(Template)]
#[template(
    syntax = "rs",
    escape = "none",
    path = "alicorn/scaffolding_template.rs"
)]
pub struct RustAlicornScaffolding<'a> {
    ci: &'a ComponentInterface,
    udl_base_name: &'a str,
}
impl<'a> RustAlicornScaffolding<'a> {
    pub fn new(ci: &'a ComponentInterface, udl_base_name: &'a str) -> Self {
        Self { ci, udl_base_name }
    }
}
mod filters {
    use super::*;

    pub fn type_alicorn(type_: &Type, ci: &ComponentInterface) -> Result<String, Error> {
        Ok(match type_ {
            Type::Int8 => "host-i8".into(),
            Type::UInt8 => "host-u8".into(),
            Type::Int16 => "host-i16".into(),
            Type::UInt16 => "host-u16".into(),
            Type::Int32 => "host-i32".into(),
            Type::UInt32 => "host-u32".into(),
            Type::Int64 => "host-i64".into(),
            Type::UInt64 => "host-u64".into(),
            Type::Float32 => "host-f32".into(),
            Type::Float64 => "host-f64".into(),
            Type::Boolean => "host-bool".into(),
            Type::String => "host-string".into(),
            Type::Bytes => return Err(Error::Custom(anyhow!("bytes unimplemented!").into())),
            Type::Timestamp => return Err(Error::Custom(anyhow!("timestamp unimplemented!").into())),
            Type::Duration => return Err(Error::Custom(anyhow!("duration unimplemented!").into())),
            Type::Enum { name, .. } | Type::Record { name, .. } => format!("r#{name}"),
            Type::Object { name, imp, .. } => {
                format!("uniffi-alicorn-{}-host-objects.uniffi-alicorn-{}-host-object-{}.t", ci.namespace(), ci.namespace(), name.to_kebab_case())
            }
            Type::CallbackInterface { name, .. } => format!("Box<dyn r#{name}>"),
            Type::Optional { inner_type } => {
                format!("(option {})", type_alicorn(inner_type, ci)?)
            }
            Type::Sequence { inner_type } => return Err(Error::Custom(anyhow!("sequence unimplemented!").into())),
            Type::Map {
                key_type,
                value_type,
            } => return Err(Error::Custom(anyhow!("map unimplemented!").into())),
            Type::Custom { name, .. } => format!("r#{name}"),
        })
    }

    pub fn type_rs(type_: &Type) -> Result<String, rinja::Error> {
        Ok(match type_ {
            Type::Int8 => "i8".into(),
            Type::UInt8 => "u8".into(),
            Type::Int16 => "i16".into(),
            Type::UInt16 => "u16".into(),
            Type::Int32 => "i32".into(),
            Type::UInt32 => "u32".into(),
            Type::Int64 => "i64".into(),
            Type::UInt64 => "u64".into(),
            Type::Float32 => "f32".into(),
            Type::Float64 => "f64".into(),
            Type::Boolean => "bool".into(),
            Type::String => "::std::string::String".into(),
            Type::Bytes => "::std::vec::Vec<u8>".into(),
            Type::Timestamp => "::std::time::SystemTime".into(),
            Type::Duration => "::std::time::Duration".into(),
            Type::Enum { name, .. } | Type::Record { name, .. } => format!("r#{name}"),
            Type::Object { name, imp, .. } => {
                format!("::std::sync::Arc<{}>", imp.rust_name_for(name))
            }
            Type::CallbackInterface { name, .. } => format!("Box<dyn r#{name}>"),
            Type::Optional { inner_type } => {
                format!("::std::option::Option<{}>", type_rs(inner_type)?)
            }
            Type::Sequence { inner_type } => format!("std::vec::Vec<{}>", type_rs(inner_type)?),
            Type::Map {
                key_type,
                value_type,
            } => format!(
                "::std::collections::HashMap<{}, {}>",
                type_rs(key_type)?,
                type_rs(value_type)?
            ),
            Type::Custom { name, .. } => format!("r#{name}"),
        })
    }
}
