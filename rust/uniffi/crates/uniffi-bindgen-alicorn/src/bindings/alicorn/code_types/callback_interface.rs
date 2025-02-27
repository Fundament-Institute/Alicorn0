// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use super::CodeType;
use uniffi_bindgen::interface;

#[derive(Debug)]
pub struct CallbackInterface {
    id: String,
}

impl CallbackInterface {
    pub fn new(id: String) -> Self {
        Self { id }
    }
}

impl CodeType for CallbackInterface {
    fn canonical_name(&self) -> String {
        format!("type-{}", self.type_label())
    }
}

impl From<interface::CallbackInterface> for CallbackInterface {
    fn from(value: interface::CallbackInterface) -> Self {
        CallbackInterface::new(value.name().into())
    }
}

impl TryFrom<interface::Type> for CallbackInterface {
    type Error = anyhow::Error;

    fn try_from(value: interface::Type) -> Result<Self, Self::Error> {
        Ok(match value {
            interface::Type::CallbackInterface { name, .. } => Self::new(name),
            _ => anyhow::bail!("Expected Type::CallbackInterface"),
        })
    }
}
