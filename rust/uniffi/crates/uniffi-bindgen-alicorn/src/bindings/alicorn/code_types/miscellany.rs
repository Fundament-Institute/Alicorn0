// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use super::CodeType;
use uniffi_bindgen::interface;

macro_rules! impl_code_type_for_miscellany {
    ($T:ident, $class_name:literal, $canonical_name:literal) => {
        #[derive(Debug)]
        pub struct $T;

        impl CodeType for $T {
            fn type_label(&self) -> String {
                $class_name.into()
            }

            fn canonical_name(&self) -> String {
                $canonical_name.into()
            }
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
}

impl_code_type_for_miscellany!(Timestamp, "ffi-timestamp", "timestamp");

impl_code_type_for_miscellany!(Duration, "ffi-duration", "duration");
