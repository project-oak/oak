//
// Copyright 2024 The Project Oak Authors
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

// This module provides a uniform way to import crypto protos regardless of
// building with cargo or bazel.

// Prost generated code cannot build on its own: it needs to be
// included into a manually crafted module structure. With crypto_rust_prost,
// this is not needed.

// TODO: b/333064338 - Remove this crate once we've stopped using cargo.

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(never_type)]

macro_rules! include_proto {
    ($package: tt) => {
        include!(concat!(env!("OUT_DIR"), concat!("/", $package, ".rs")));
        #[cfg(feature = "json")]
        include!(concat!(env!("OUT_DIR"), "/", $package, ".serde.rs"));
    };
}

pub mod oak {
    // Do not lint generated code.
    #![allow(clippy::all, clippy::pedantic, clippy::nursery)]

    include_proto!("oak");

    pub mod attestation {
        pub mod v1 {
            include_proto!("oak.attestation.v1");
            extern crate alloc;
            use alloc::{format, string::String};

            use prost::Name;

            const PACKAGE: &str = "oak.attestation.v1";

            /// Compute the type URL for the given `oak.attestation.v1` type,
            /// using `type.googleapis.com` as the authority for the
            /// URL.
            fn type_url_for<T: Name>() -> String {
                format!("type.googleapis.com/{}.{}", T::PACKAGE, T::NAME)
            }

            impl Name for Stage0Measurements {
                const PACKAGE: &'static str = PACKAGE;
                const NAME: &'static str = "Stage0";

                fn type_url() -> String {
                    type_url_for::<Self>()
                }
            }
        }
    }

    pub mod crypto {
        pub mod v1 {
            include_proto!("oak.crypto.v1");
        }
    }

    pub mod oak_functions {
        pub mod abi {
            include_proto!("oak.functions.abi");
        }
        pub mod lookup_data {
            include_proto!("oak.functions.lookup_data");
        }
        pub mod testing {
            use prost::Message;
            include_proto!("oak.functions.testing");
        }
    }

    pub mod session {
        pub mod v1 {
            #![allow(dead_code)]
            include_proto!("oak.session.v1");
        }
    }
}

/// Well known proto messages use a different type depending on whether JSON
/// mappings are enabled. This can cause type checking issues when this crate
/// is used. To address this we export relevant utilites whose implementation
/// depends on which feature is set for this crate.
/// This is similiar to the approach taken by serde for an analogous issue: https://docs.rs/serde/1.0.186/src/serde/integer128.rs.html#71-75
pub mod well_known {
    // Copied implementation from prost types: https://github.com/tokio-rs/prost/blob/d42c85e790263f78f6c626ceb0dac5fda0edcb41/prost-types/src/any.rs#L4
    // as pbjson-types's Any does not implenment a similiar function.
    #[cfg(feature = "json")]
    pub fn any_from_msg<M>(msg: &M) -> Result<pbjson_types::Any, prost::EncodeError>
    where
        M: prost::Name,
    {
        let type_url = M::type_url();
        let mut value = Vec::new();
        prost::Message::encode(msg, &mut value)?;
        Ok(pbjson_types::Any { type_url, value: value.into() })
    }

    #[cfg(not(feature = "json"))]
    pub fn any_from_msg<M>(msg: &M) -> Result<prost_types::Any, prost::EncodeError>
    where
        M: prost::Name,
    {
        prost_types::Any::from_msg(msg)
    }
}
