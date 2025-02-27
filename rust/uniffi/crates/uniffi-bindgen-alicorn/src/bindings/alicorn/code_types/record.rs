// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use super::{CodeOracle, CodeType};
use uniffi_bindgen::interface;

#[derive(Debug)]
pub struct Record {
    id: String,
}

impl Record {
    pub fn new(id: String) -> Self {
        Self { id }
    }
}

impl CodeType for Record {
    fn type_label(&self) -> String {
        CodeOracle.class_name(&*self.id)
    }

    fn canonical_name(&self) -> String {
        format!("type-{}", self.type_label())
    }
}

impl TryFrom<interface::Type> for Record {
    type Error = anyhow::Error;

    fn try_from(value: interface::Type) -> Result<Self, Self::Error> {
        Ok(match value {
            interface::Type::Record { name, .. } => Self::new(name),
            _ => anyhow::bail!("Expected Type::Record"),
        })
    }
}
