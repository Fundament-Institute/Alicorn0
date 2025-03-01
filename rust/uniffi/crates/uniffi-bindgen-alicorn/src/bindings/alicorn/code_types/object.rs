// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use super::{CodeOracle, CodeType};
use uniffi_bindgen::interface;

#[derive(Debug)]
pub struct Object {
    name: String,
    imp: interface::ObjectImpl,
}

impl Object {
    pub fn new(name: String, imp: interface::ObjectImpl) -> Self {
        Self { name, imp }
    }
}

impl CodeType for Object {
    fn type_label(&self) -> String {
        CodeOracle.class_name(&*self.name)
    }

    fn canonical_name(&self) -> String {
        format!("type-{}", self.type_label())
    }

    fn initialization_fn(&self) -> Option<String> {
        self.imp
            .has_callback_interface()
            .then(|| format!("uniffi-callback-interfaces.{}.register", self.type_label()))
    }
}

impl From<interface::Object> for Object {
    fn from(value: interface::Object) -> Self {
        Object::new(value.name().into(), value.imp().clone())
    }
}

impl TryFrom<interface::Type> for Object {
    type Error = anyhow::Error;

    fn try_from(value: interface::Type) -> Result<Self, Self::Error> {
        Ok(match value {
            interface::Type::Object { name, imp, .. } => Self::new(name, imp),
            _ => anyhow::bail!("Expected Type::Object"),
        })
    }
}
