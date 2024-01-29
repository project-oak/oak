//
// Copyright 2022 The Project Oak Authors
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

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(never_type)]
#![feature(unwrap_infallible)]
// Required for enabling benchmark tests.
#![feature(test)]

extern crate alloc;

#[cfg(test)]
extern crate std;

pub mod proto {
    pub mod oak {
        pub use oak_attestation::proto::oak::attestation;
        pub use oak_crypto::proto::oak::crypto;
        pub mod functions {
            #![allow(dead_code)]
            use prost::Message;
            include!(concat!(env!("OUT_DIR"), "/oak.functions.rs"));
        }
    }
}

pub mod instance;
pub mod logger;
pub mod lookup;
pub mod wasm;

pub trait Observer {
    fn wasm_initialization(&self, duration: core::time::Duration);
    fn wasm_invocation(&self, duration: core::time::Duration);
}
