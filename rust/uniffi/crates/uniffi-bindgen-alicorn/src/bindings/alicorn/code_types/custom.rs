// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use super::{CodeOracle, CodeType};
use uniffi_bindgen::interface;

#[derive(Debug)]
pub struct Custom {
    name: String,
}

impl Custom {
    pub fn new(name: String) -> Self {
        Custom { name }
    }
}

impl CodeType for Custom {
    fn type_label(&self) -> String {
        CodeOracle.class_name(&*self.name)
    }

    fn canonical_name(&self) -> String {
        format!("custom-{}", self.type_label())
    }
}

impl TryFrom<interface::Type> for Custom {
    type Error = anyhow::Error;

    fn try_from(value: interface::Type) -> Result<Self, Self::Error> {
        Ok(match value {
            interface::Type::Custom { name, .. } => Self::new(name),
            _ => anyhow::bail!("Expected Type::Custom"),
        })
    }
}
