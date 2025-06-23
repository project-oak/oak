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

pub mod oak {
    pub mod private_memory {
        tonic::include_proto!("oak.private_memory");
    }

    use oak_proto_rust::oak::session;
}

pub mod base64data {
    use base64::{engine::general_purpose::STANDARD, Engine as _};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    extern crate alloc;
    use alloc::{string::String, vec::Vec};

    pub fn serialize<S: Serializer>(v: &[u8], s: S) -> Result<S::Ok, S::Error> {
        let base64_str = STANDARD.encode(v);
        String::serialize(&base64_str, s)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<u8>, D::Error> {
        let base64_str = String::deserialize(d)?;
        STANDARD.decode(base64_str.as_bytes()).map_err(serde::de::Error::custom)
    }
}

pub mod key_sync_response_status_converter {
    use serde::{
        de::{self, Visitor},
        Deserializer, Serializer,
    };

    pub fn serialize<S: Serializer>(v: &i32, s: S) -> Result<S::Ok, S::Error> {
        use crate::oak::private_memory::key_sync_response::Status;
        let v = Status::try_from(*v);
        if let Ok(v) = v {
            s.serialize_str(v.as_str_name())
        } else {
            s.serialize_str(Status::Unspecified.as_str_name())
        }
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<i32, D::Error>
    where
        D: Deserializer<'de>,
    {
        use crate::oak::private_memory::key_sync_response::Status;

        struct StatusVisitor;

        impl Visitor<'_> for StatusVisitor {
            type Value = i32;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str(
                    "a string or an integer representing a key_sync_response::Status variant",
                )
            }

            fn visit_str<'s, E>(self, value: &str) -> Result<i32, E>
            where
                E: de::Error,
            {
                let v = Status::from_str_name(value);
                if let Some(v) = v {
                    Ok(v as i32)
                } else {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Str(value),
                        &"a valid string for key_sync_response::Status variant",
                    ))
                }
            }
            fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if crate::oak::private_memory::key_sync_response::Status::try_from(value).is_ok() {
                    Ok(value)
                } else {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Signed(value as i64),
                        &"a valid integer for key_sync_response::Status variant",
                    ))
                }
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if v <= i32::MAX as u64 {
                    self.visit_i32(v as i32)
                } else {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Unsigned(v),
                        &"an integer value fitting in i32 for key_sync_response::Status",
                    ))
                }
            }

            fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if v >= i32::MIN as i64 && v <= i32::MAX as i64 {
                    self.visit_i32(v as i32)
                } else {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Signed(v),
                        &"an integer value fitting in i32 for key_sync_response::Status",
                    ))
                }
            }
        }
        deserializer.deserialize_any(StatusVisitor)
    }
}

pub mod user_registration_response_status_converter {
    use serde::{
        de::{self, Visitor},
        Deserializer, Serializer,
    };

    pub fn serialize<S: Serializer>(v: &i32, s: S) -> Result<S::Ok, S::Error> {
        use crate::oak::private_memory::user_registration_response::Status;
        let status_enum = Status::try_from(*v);
        if let Ok(status) = status_enum {
            s.serialize_str(status.as_str_name())
        } else {
            s.serialize_str(Status::Unspecified.as_str_name())
        }
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<i32, D::Error>
    where
        D: Deserializer<'de>,
    {
        use crate::oak::private_memory::user_registration_response::Status;

        struct StatusVisitor;

        impl Visitor<'_> for StatusVisitor {
            type Value = i32;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a string or an integer representing a UserRegistrationResponse::Status variant")
            }

            fn visit_str<'s, E>(self, value: &str) -> Result<i32, E>
            where
                E: de::Error,
            {
                match Status::from_str_name(value) {
                    Some(status) => Ok(status as i32),
                    None => Err(de::Error::unknown_variant(
                        value,
                        &["UNSPECIFIED", "SUCCESS", "USER_ALREADY_EXISTS"],
                    )),
                }
            }

            fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if Status::try_from(value).is_ok() {
                    Ok(value)
                } else {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Signed(value as i64),
                        &"a valid integer for UserRegistrationResponse::Status variant",
                    ))
                }
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if v <= i32::MAX as u64 {
                    self.visit_i32(v as i32)
                } else {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Unsigned(v),
                        &"an integer value fitting in i32 for UserRegistrationResponse::Status",
                    ))
                }
            }

            fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if v >= i32::MIN as i64 && v <= i32::MAX as i64 {
                    self.visit_i32(v as i32)
                } else {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Signed(v),
                        &"an integer value fitting in i32 for UserRegistrationResponse::Status",
                    ))
                }
            }
        }
        deserializer.deserialize_any(StatusVisitor)
    }
}

pub mod memory_field_converter {
    use serde::{
        de::{self, SeqAccess, Visitor},
        Deserialize, Deserializer, Serializer,
    };

    use crate::oak::private_memory::MemoryField;
    extern crate alloc;
    use alloc::vec::Vec;
    pub fn serialize<S: Serializer>(v_list: &Vec<i32>, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeSeq;

        let mut seq = s.serialize_seq(Some(v_list.len()))?;
        for val in v_list {
            let field_enum = MemoryField::try_from(*val).ok();
            let str_val = if let Some(field) = field_enum {
                field.as_str_name()
            } else {
                MemoryField::Unknown.as_str_name()
            };
            seq.serialize_element(str_val)?;
        }
        seq.end()
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<i32>, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct VecMemoryFieldVisitor;

        impl<'de> Visitor<'de> for VecMemoryFieldVisitor {
            type Value = Vec<i32>;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str(
                    "a sequence of strings or integers representing MemoryField variants",
                )
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut vec = Vec::new();
                while let Some(element) = seq.next_element::<MemoryFieldElement>()? {
                    vec.push(element.0);
                }
                Ok(vec)
            }
        }
        deserializer.deserialize_seq(VecMemoryFieldVisitor)
    }

    struct MemoryFieldElement(i32);

    impl<'de> Deserialize<'de> for MemoryFieldElement {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            struct ElementVisitor;

            impl Visitor<'_> for ElementVisitor {
                type Value = i32;

                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str("a string or an integer representing a MemoryField variant")
                }

                fn visit_str<E>(self, value: &str) -> Result<i32, E>
                where
                    E: de::Error,
                {
                    match MemoryField::from_str_name(value) {
                        Some(field) => Ok(field as i32),
                        None => Err(de::Error::unknown_variant(
                            value,
                            &["UNKNOWN", "ID", "TAGS", "EMBEDDINGS", "CONTENT"],
                        )),
                    }
                }

                fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    if MemoryField::try_from(value).is_ok() {
                        Ok(value)
                    } else {
                        Err(de::Error::invalid_value(
                            de::Unexpected::Signed(value as i64),
                            &"a valid integer for MemoryField variant",
                        ))
                    }
                }

                fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    if v <= i32::MAX as u64 {
                        self.visit_i32(v as i32)
                    } else {
                        Err(de::Error::invalid_value(
                            de::Unexpected::Unsigned(v),
                            &"an integer value fitting in i32 for MemoryField",
                        ))
                    }
                }

                fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    if v >= i32::MIN as i64 && v <= i32::MAX as i64 {
                        self.visit_i32(v as i32)
                    } else {
                        Err(de::Error::invalid_value(
                            de::Unexpected::Signed(v),
                            &"an integer value fitting in i32 for MemoryField",
                        ))
                    }
                }
            }
            Ok(MemoryFieldElement(deserializer.deserialize_any(ElementVisitor)?))
        }
    }
}

pub mod embedding_query_metric_type_converter {
    use serde::{
        de::{self, Visitor},
        Deserializer, Serializer,
    };
    extern crate alloc;

    pub fn serialize<S: Serializer>(v: &i32, s: S) -> Result<S::Ok, S::Error> {
        use crate::oak::private_memory::EmbeddingQueryMetricType;
        let metric_enum = EmbeddingQueryMetricType::try_from(*v);
        if let Ok(metric) = metric_enum {
            s.serialize_str(metric.as_str_name())
        } else {
            s.serialize_str(EmbeddingQueryMetricType::DotProduct.as_str_name())
        }
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<i32, D::Error>
    where
        D: Deserializer<'de>,
    {
        use crate::oak::private_memory::EmbeddingQueryMetricType;

        struct MetricTypeVisitor;

        impl Visitor<'_> for MetricTypeVisitor {
            type Value = i32;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str(
                    "a string or an integer representing an EmbeddingQueryMetricType variant",
                )
            }

            fn visit_str<'s, E>(self, value: &str) -> Result<i32, E>
            where
                E: de::Error,
            {
                match EmbeddingQueryMetricType::from_str_name(value) {
                    Some(metric) => Ok(metric as i32),
                    None => Err(de::Error::unknown_variant(value, &["DOT_PRODUCT"])),
                }
            }

            fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if EmbeddingQueryMetricType::try_from(value).is_ok() {
                    Ok(value)
                } else {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Signed(value as i64),
                        &"a valid integer for EmbeddingQueryMetricType variant",
                    ))
                }
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if v <= i32::MAX as u64 {
                    self.visit_i32(v as i32)
                } else {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Unsigned(v),
                        &"an integer value fitting in i32 for EmbeddingQueryMetricType",
                    ))
                }
            }

            fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if v >= i32::MIN as i64 && v <= i32::MAX as i64 {
                    self.visit_i32(v as i32)
                } else {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Signed(v),
                        &"an integer value fitting in i32 for EmbeddingQueryMetricType",
                    ))
                }
            }
        }
        deserializer.deserialize_any(MetricTypeVisitor)
    }
}
