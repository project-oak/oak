//
// Copyright 2025 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
use base64::{Engine as _, engine::general_purpose::STANDARD};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
extern crate alloc;
use alloc::{string::String, vec::Vec};
use core::fmt;

use serde::de::Visitor;
pub fn serialize<S: Serializer>(v: &[u8], s: S) -> Result<S::Ok, S::Error> {
    let base64_str = STANDARD.encode(v);
    String::serialize(&base64_str, s)
}
pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<u8>, D::Error> {
    let base64_str = String::deserialize(d)?;
    STANDARD.decode(base64_str.as_bytes()).map_err(serde::de::Error::custom)
}
pub mod option_bytes {
    use super::*;
    pub fn serialize<S: Serializer>(v: &Option<Vec<u8>>, s: S) -> Result<S::Ok, S::Error> {
        match v {
            Some(v) => {
                let base64_str = STANDARD.encode(v);
                String::serialize(&base64_str, s)
            }
            None => s.serialize_none(),
        }
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Option<Vec<u8>>, D::Error> {
        struct OptionVisitor;
        impl<'de> Visitor<'de> for OptionVisitor {
            type Value = Option<Vec<u8>>;
            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("an optional base64-encoded string or null")
            }
            fn visit_some<D>(self, d: D) -> Result<Self::Value, D::Error>
            where
                D: Deserializer<'de>,
            {
                let base64_str = String::deserialize(d)?;
                let decoded =
                    STANDARD.decode(base64_str.as_bytes()).map_err(serde::de::Error::custom)?;
                Ok(Some(decoded))
            }
            fn visit_none<E>(self) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(None)
            }
        }
        d.deserialize_option(OptionVisitor)
    }
}

pub mod repeated_bytes {
    use alloc::vec::Vec;

    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    use super::*;

    pub fn serialize<S: Serializer>(v: &[Vec<u8>], s: S) -> Result<S::Ok, S::Error> {
        let base64_strings: Vec<String> = v.iter().map(|bytes| STANDARD.encode(bytes)).collect();
        base64_strings.serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<Vec<u8>>, D::Error> {
        let base64_strings: Vec<String> = Vec::deserialize(d)?;
        base64_strings
            .into_iter()
            .map(|s| STANDARD.decode(s.as_bytes()).map_err(serde::de::Error::custom))
            .collect()
    }
}
