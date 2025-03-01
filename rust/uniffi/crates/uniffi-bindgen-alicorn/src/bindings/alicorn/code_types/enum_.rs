// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use super::{CodeOracle, CodeType};
use uniffi_bindgen::interface;

#[derive(Debug)]
pub struct Enum {
    id: String,
}

impl Enum {
    pub fn new(id: String) -> Self {
        Self { id }
    }
}

impl CodeType for Enum {
    fn type_label(&self) -> String {
        CodeOracle.class_name(&*self.id)
    }

    fn canonical_name(&self) -> String {
        format!("type-{}", self.type_label())
    }
}

impl From<interface::Enum> for Enum {
    fn from(value: interface::Enum) -> Self {
        Enum::new(value.name().into())
    }
}

impl TryFrom<interface::Type> for Enum {
    type Error = anyhow::Error;

    fn try_from(value: interface::Type) -> Result<Self, Self::Error> {
        Ok(match value {
            interface::Type::Enum { name, .. } => Self::new(name),
            _ => anyhow::bail!("Expected Type::Enum"),
        })
    }
}

#[derive(Debug)]
pub struct Variant {
    v: interface::Variant,
}

impl Variant {
    pub fn name(&self) -> &str {
        self.v.name()
    }
}

impl CodeType for Variant {
    fn type_label(&self) -> String {
        CodeOracle.class_name(self.name())
    }

    fn canonical_name(&self) -> String {
        self.type_label().into()
    }
}

impl From<interface::Variant> for Variant {
    fn from(value: interface::Variant) -> Self {
        Self { v: value }
    }
}
