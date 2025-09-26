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

// Prost generated code cannot build on its own: it needs to be
// included into a manually crafted module structure. With crypto_rust_prost,
// this is not needed.

// TODO: b/333064338 - Remove this crate once we've stopped using cargo.

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(never_type)]

macro_rules! include_proto {
    ($package: tt) => {
        include!(concat!(env!("OUT_DIR"), concat!("/", $package, ".rs")));
    };
}

pub mod perftools {
    pub mod profiles {
        include_proto!("perftools.profiles");
    }
}

pub mod attestation;
pub mod base64data;
pub mod certificate;
pub mod variant;

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
                const NAME: &'static str = "Stage0Measurements";

                fn type_url() -> String {
                    type_url_for::<Self>()
                }
            }
        }
    }

    pub mod containers {
        include_proto!("oak.containers");
        pub mod v1 {
            include_proto!("oak.containers.v1");
        }
    }

    pub mod ctf_sha2 {
        include_proto!("oak.ctf_sha2");
    }

    pub mod debug {
        include_proto!("oak.debug");
    }

    pub mod crypto {
        pub mod v1 {
            include_proto!("oak.crypto.v1");
        }
    }

    pub mod functions {
        include_proto!("oak.functions");
        pub mod abi {
            include_proto!("oak.functions.abi");
        }
        pub mod config {
            include_proto!("oak.functions.config");
        }
        pub mod lookup_data {
            include_proto!("oak.functions.lookup_data");
        }
        pub mod standalone {
            include_proto!("oak.functions.standalone");
        }
        pub mod testing {
            include_proto!("oak.functions.testing");
        }

        pub mod wasm {
            pub mod v1 {
                include_proto!("oak.functions.wasm.v1");
            }
        }
    }

    pub mod key_provisioning {
        pub mod v1 {
            include_proto!("oak.key_provisioning.v1");
        }
    }

    pub mod packages {
        include_proto!("oak.packages");
    }

    pub mod restricted_kernel {
        include_proto!("oak.restricted_kernel");
    }

    pub mod session {
        pub mod v1 {
            #![allow(dead_code)]
            include_proto!("oak.session.v1");
        }
    }

    pub mod verity {
        include_proto!("oak.verity");
    }
}
