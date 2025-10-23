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
//

#![no_std]
#![feature(never_type)]

pub mod oak {
    pub mod attestation {
        pub mod v1 {
            pub use oak_proto_rust::oak::attestation::v1::Evidence;
        }
    }
    pub mod ctf_sha2 {
        pub mod enclave {
            #![allow(dead_code)]
            #![allow(clippy::let_unit_value)]

            use prost::Message;
            include!(concat!(env!("OUT_DIR"), "/oak.ctf_sha2.enclave.rs"));
        }
    }
}
