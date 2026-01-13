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

pub mod prelude;

pub mod google {
    pub mod rpc {
        tonic::include_proto!("google.rpc");
    }
}

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

/// Defines a deserializer for a Protobuf enum that can handle both integer and
/// string representations.
///
/// # Input
/// - `enum_type`: The type of the Protobuf-generated enum.
/// - `doc_string`: A docstring used in error messages to describe the expected
///   value.
/// - `valid_variants`: A slice of strings containing the names of the valid
///   enum variants, used for error reporting.
///
/// # Output
/// This macro generates a struct `EnumElement(pub i32)` and implements the
/// `serde::Deserialize` trait for it. The implementation can deserialize from
/// either a string (e.g., "SUCCESS") or an integer representing the enum
/// variant.
macro_rules! define_enum_element_deserializer {
    (
        enum_type = $enum_type:ty,
        doc_string = $doc_string:expr,
        valid_variants = $valid_variants:expr
    ) => {
        use serde::{
            de::{self, Visitor},
            Deserialize, Deserializer,
        };

        struct EnumElement(pub i32);

        impl<'de> Deserialize<'de> for EnumElement {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct ElementVisitor;

                impl<'de> Visitor<'de> for ElementVisitor {
                    type Value = i32;

                    fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                        formatter.write_str($doc_string)
                    }

                    fn visit_str<E>(self, value: &str) -> Result<i32, E>
                    where
                        E: de::Error,
                    {
                        match <$enum_type>::from_str_name(value) {
                            Some(field) => Ok(field as i32),
                            None => Err(de::Error::unknown_variant(value, $valid_variants)),
                        }
                    }

                    fn visit_i32<E>(self, value: i32) -> Result<Self::Value, E>
                    where
                        E: de::Error,
                    {
                        if <$enum_type>::try_from(value).is_ok() {
                            Ok(value)
                        } else {
                            Err(de::Error::invalid_value(
                                de::Unexpected::Signed(value as i64),
                                &$doc_string,
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
                            Err(de::Error::invalid_value(de::Unexpected::Unsigned(v), &$doc_string))
                        }
                    }

                    fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
                    where
                        E: de::Error,
                    {
                        if v >= i32::MIN as i64 && v <= i32::MAX as i64 {
                            self.visit_i32(v as i32)
                        } else {
                            Err(de::Error::invalid_value(de::Unexpected::Signed(v), &$doc_string))
                        }
                    }
                }
                Ok(EnumElement(deserializer.deserialize_any(ElementVisitor)?))
            }
        }
    };
}

/// Creates a module with `serialize` and `deserialize` functions for a
/// Protobuf enum field.
///
/// This is intended to be used with `serde(with = "...")` to handle the
/// serialization of an enum to its string name and deserialization from either
/// its string name or integer value.
///
/// # Input
/// - `module_name`: The name for the generated module.
/// - `enum_type`: The type of the Protobuf-generated enum.
/// - `unspecified_variant`: The enum variant to use as a fallback for unknown
///   values during serialization.
/// - `doc_string`: A docstring used in error messages.
/// - `valid_variants`: A slice of strings containing the names of the valid
///   enum variants.
///
/// # Output
/// This macro generates a module containing `serialize` and `deserialize`
/// functions.
/// - `serialize`: Converts an `&i32` representing an enum variant to its string
///   name.
/// - `deserialize`: Converts a string or integer into an `i32` representing an
///   enum variant.
macro_rules! enum_converter {
    (
        module_name = $module_name:ident,
        enum_type = $enum_type:ty,
        unspecified_variant = $unspecified_variant:expr,
        doc_string = $doc_string:expr,
        valid_variants = $valid_variants:expr
    ) => {
        pub mod $module_name {
            use serde::Serializer;

            define_enum_element_deserializer!(
                enum_type = $enum_type,
                doc_string = $doc_string,
                valid_variants = $valid_variants
            );

            pub fn serialize<S: Serializer>(v: &i32, s: S) -> Result<S::Ok, S::Error> {
                let v = <$enum_type>::try_from(*v);
                if let Ok(v) = v {
                    s.serialize_str(v.as_str_name())
                } else {
                    s.serialize_str($unspecified_variant.as_str_name())
                }
            }

            pub fn deserialize<'de, D>(deserializer: D) -> Result<i32, D::Error>
            where
                D: serde::de::Deserializer<'de>,
            {
                EnumElement::deserialize(deserializer).map(|e| e.0)
            }
        }
    };
}

/// Creates a module with `serialize` and `deserialize` functions for a `Vec` of
/// Protobuf enum fields.
///
/// This is intended to be used with `serde(with = "...")` to handle the
/// serialization of a vector of enums to a sequence of their string names, and
/// deserialization from a sequence of either string names or integer values.
///
/// # Input
/// - `module_name`: The name for the generated module.
/// - `enum_type`: The type of the Protobuf-generated enum.
/// - `unspecified_variant`: The enum variant to use as a fallback for unknown
///   values during serialization.
/// - `doc_string`: A docstring for error messages when expecting the sequence.
/// - `element_doc_string`: A docstring for error messages when expecting a
///   single element.
/// - `valid_variants`: A slice of strings containing the names of the valid
///   enum variants.
///
/// # Output
/// This macro generates a module containing `serialize` and `deserialize`
/// functions for a `Vec<i32>`.
/// - `serialize`: Converts a `&Vec<i32>` to a sequence of string names.
/// - `deserialize`: Converts a sequence of strings or integers into a
///   `Vec<i32>`.
macro_rules! vec_enum_converter {
    (
        module_name = $module_name:ident,
        enum_type = $enum_type:ty,
        unspecified_variant = $unspecified_variant:expr,
        doc_string = $doc_string:expr,
        element_doc_string = $element_doc_string:expr,
        valid_variants = $valid_variants:expr
    ) => {
        pub mod $module_name {
            use serde::{ser::SerializeSeq, Serializer};
            extern crate alloc;
            use alloc::vec::Vec;

            define_enum_element_deserializer!(
                enum_type = $enum_type,
                doc_string = $element_doc_string,
                valid_variants = $valid_variants
            );

            pub fn serialize<S: Serializer>(v_list: &Vec<i32>, s: S) -> Result<S::Ok, S::Error> {
                let mut seq = s.serialize_seq(Some(v_list.len()))?;
                for val in v_list {
                    let field_enum = <$enum_type>::try_from(*val).ok();
                    let str_val = if let Some(field) = field_enum {
                        field.as_str_name()
                    } else {
                        $unspecified_variant.as_str_name()
                    };
                    seq.serialize_element(str_val)?;
                }
                seq.end()
            }

            pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<i32>, D::Error>
            where
                D: serde::de::Deserializer<'de>,
            {
                struct VecEnumVisitor;

                impl<'de> serde::de::Visitor<'de> for VecEnumVisitor {
                    type Value = Vec<i32>;

                    fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                        formatter.write_str($doc_string)
                    }

                    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                    where
                        A: serde::de::SeqAccess<'de>,
                    {
                        let mut vec = Vec::new();
                        while let Some(element) = seq.next_element::<EnumElement>()? {
                            vec.push(element.0);
                        }
                        Ok(vec)
                    }
                }
                deserializer.deserialize_seq(VecEnumVisitor)
            }
        }
    };
}

enum_converter!(
    module_name = key_sync_response_status_converter,
    enum_type = crate::oak::private_memory::key_sync_response::Status,
    unspecified_variant = crate::oak::private_memory::key_sync_response::Status::Unspecified,
    doc_string = "a string or an integer representing a key_sync_response::Status variant",
    valid_variants = &["UNSPECIFIED", "SUCCESS", "INVALID_KEY", "INVALID_PM_UID"]
);

enum_converter!(
    module_name = user_registration_response_status_converter,
    enum_type = crate::oak::private_memory::user_registration_response::Status,
    unspecified_variant =
        crate::oak::private_memory::user_registration_response::Status::Unspecified,
    doc_string = "a string or an integer representing a UserRegistrationResponse::Status variant",
    valid_variants = &["UNSPECIFIED", "SUCCESS", "USER_ALREADY_EXISTS"]
);

vec_enum_converter!(
    module_name = memory_field_converter,
    enum_type = crate::oak::private_memory::MemoryField,
    unspecified_variant = crate::oak::private_memory::MemoryField::Unknown,
    doc_string = "a sequence of strings or integers representing MemoryField variants",
    element_doc_string = "a string or an integer representing a MemoryField variant",
    valid_variants = &[
        "UNKNOWN",
        "ID",
        "TAGS",
        "EMBEDDINGS",
        "CONTENT",
        "CREATED_TIMESTAMP",
        "EVENT_TIMESTAMP",
        "EXPIRED_TIMESTAMP"
    ]
);

enum_converter!(
    module_name = embedding_query_metric_type_converter,
    enum_type = crate::oak::private_memory::EmbeddingQueryMetricType,
    unspecified_variant = crate::oak::private_memory::EmbeddingQueryMetricType::DotProduct,
    doc_string = "a string or an integer representing an EmbeddingQueryMetricType variant",
    valid_variants = &["DOT_PRODUCT"]
);

enum_converter!(
    module_name = text_query_match_type_converter,
    enum_type = crate::oak::private_memory::MatchType,
    unspecified_variant = crate::oak::private_memory::MatchType::Unspecified,
    doc_string = "a string or an integer representing a TextQuery::MatchType variant",
    valid_variants = &["UNSPECIFIED", "EQUAL", "GTE", "LTE", "LT", "GT"]
);

enum_converter!(
    module_name = operator_converter,
    enum_type = crate::oak::private_memory::QueryOperator,
    unspecified_variant = crate::oak::private_memory::QueryOperator::default(),
    doc_string = "a string or an integer representing an Operator variant",
    valid_variants = &["OPERATOR_UNSPECIFIED", "OPERATOR_AND", "OPERATOR_OR"]
);

pub mod timestamp_converter {
    use chrono::{DateTime, Utc};
    use prost_types::Timestamp;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    extern crate alloc;
    use alloc::string::String;

    pub fn serialize<S: Serializer>(
        timestamp: &Option<Timestamp>,
        s: S,
    ) -> Result<S::Ok, S::Error> {
        if let Some(ref ts) = timestamp {
            let datetime = DateTime::<Utc>::from_timestamp(ts.seconds, ts.nanos as u32)
                .ok_or_else(|| serde::ser::Error::custom("invalid timestamp"))?;
            return String::serialize(&datetime.to_rfc3339(), s);
        }
        s.serialize_none()
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Option<Timestamp>, D::Error> {
        let rfc3339_string: Option<String> = Option::deserialize(d)?;
        if let Some(s) = rfc3339_string {
            let datetime = DateTime::parse_from_rfc3339(&s)
                .map_err(serde::de::Error::custom)?
                .with_timezone(&Utc);
            return Ok(Some(Timestamp {
                seconds: datetime.timestamp(),
                nanos: datetime.timestamp_subsec_nanos() as i32,
            }));
        }
        Ok(None)
    }
}

pub mod non_optional_timestamp_converter {
    use chrono::{DateTime, Utc};
    use prost_types::Timestamp;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    extern crate alloc;
    use alloc::string::String;
    pub fn serialize<S: Serializer>(timestamp: &Timestamp, s: S) -> Result<S::Ok, S::Error> {
        let datetime = DateTime::<Utc>::from_timestamp(timestamp.seconds, timestamp.nanos as u32)
            .ok_or_else(|| serde::ser::Error::custom("invalid timestamp"))?;
        String::serialize(&datetime.to_rfc3339(), s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Timestamp, D::Error> {
        let rfc3339_string: String = String::deserialize(d)?;
        let datetime = DateTime::parse_from_rfc3339(&rfc3339_string)
            .map_err(serde::de::Error::custom)?
            .with_timezone(&Utc);
        Ok(Timestamp {
            seconds: datetime.timestamp(),
            nanos: datetime.timestamp_subsec_nanos() as i32,
        })
    }
}

pub mod prost_types_any_converter {
    use prost_types::Any;
    use serde::{Deserializer, Serializer};
    // google.rpc.Status contains an Any field, so we need a serializer for it.
    // But we don't currently use this field, so the implementation is a no-op
    // for now.
    //
    // If we end up using it, and supporting JSON serialization, each type we
    // intend to support will need to be explicitly handled here.
    pub fn serialize<S: Serializer>(_v: &[Any], _s: S) -> Result<S::Ok, S::Error> {
        Err(serde::ser::Error::custom("serialization of prost_types::Any is not supported yet."))
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(_d: D) -> Result<Vec<Any>, D::Error> {
        Err(serde::de::Error::custom("deserialization of prost_types::Any is not supported yet."))
    }
}
