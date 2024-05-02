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
}
