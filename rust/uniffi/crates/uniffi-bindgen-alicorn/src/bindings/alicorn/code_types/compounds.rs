// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use super::{CodeOracle, CodeType};
use uniffi_bindgen::interface;

#[derive(Debug)]
pub struct Optional {
    inner: interface::Type,
}

impl Optional {
    pub fn new(inner: interface::Type) -> Self {
        Self { inner }
    }
    fn inner(&self) -> &interface::Type {
        &self.inner
    }
}

impl CodeType for Optional {
    fn canonical_name(&self) -> String {
        format!(
            "optional-{}",
            CodeOracle.find(self.inner()).canonical_name()
        )
    }
}

impl TryFrom<interface::Type> for Optional {
    type Error = anyhow::Error;

    fn try_from(value: interface::Type) -> Result<Self, Self::Error> {
        Ok(match value {
            interface::Type::Optional { inner_type, .. } => Self::new(*inner_type),
            _ => anyhow::bail!("Expected Type::Optional"),
        })
    }
}

#[derive(Debug)]
pub struct Sequence {
    inner: interface::Type,
}

impl Sequence {
    pub fn new(inner: interface::Type) -> Self {
        Self { inner }
    }
    fn inner(&self) -> &interface::Type {
        &self.inner
    }
}

impl CodeType for Sequence {
    fn canonical_name(&self) -> String {
        format!(
            "sequence-{}",
            CodeOracle.find(self.inner()).canonical_name()
        )
    }
}

impl TryFrom<interface::Type> for Sequence {
    type Error = anyhow::Error;

    fn try_from(value: interface::Type) -> Result<Self, Self::Error> {
        Ok(match value {
            interface::Type::Sequence { inner_type, .. } => Self::new(*inner_type),
            _ => anyhow::bail!("Expected Type::Sequence"),
        })
    }
}

#[derive(Debug)]
pub struct Map {
    key: interface::Type,
    value: interface::Type,
}

impl Map {
    pub fn new(key: interface::Type, value: interface::Type) -> Self {
        Self { key, value }
    }

    fn key(&self) -> &interface::Type {
        &self.key
    }

    fn value(&self) -> &interface::Type {
        &self.value
    }
}

impl CodeType for Map {
    fn canonical_name(&self) -> String {
        format!(
            "map-{}-{}",
            CodeOracle.find(self.key()).canonical_name(),
            CodeOracle.find(self.value()).canonical_name()
        )
    }
}

impl TryFrom<interface::Type> for Map {
    type Error = anyhow::Error;

    fn try_from(value: interface::Type) -> Result<Self, Self::Error> {
        Ok(match value {
            interface::Type::Map {
                key_type,
                value_type,
                ..
            } => Self::new(*key_type, *value_type),
            _ => anyhow::bail!("Expected Type::Map"),
        })
    }
}
