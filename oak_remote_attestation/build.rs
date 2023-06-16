//
<<<<<<< HEAD
// Copyright 2023 The Project Oak Authors
=======
// Copyright 2022 The Project Oak Authors
>>>>>>> 2fb4fa7785c93ccaf9a972be96d4ad5faa15de4c
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

<<<<<<< HEAD
<<<<<<<< HEAD:oak_remote_attestation/build.rs
fn main() -> Result<(), Box<dyn std::error::Error>> {
    micro_rpc_build::compile(
        &[format!(
            "{}oak_remote_attestation/proto/v1/messages.proto",
            env!("WORKSPACE_ROOT")
        )],
        &[format!(
            "{}oak_remote_attestation/proto/v1",
            env!("WORKSPACE_ROOT")
        )],
    );

    Ok(())
}
========
//! Rust implementation of features needed to implement guest enlightenment for operating systems
//! running under Intel TDX.

#![no_std]
#![feature(split_array)]
#![deny(unsafe_op_in_unsafe_fn)]

pub mod tdcall;
pub mod vmcall;
>>>>>>>> 2fb4fa7785c93ccaf9a972be96d4ad5faa15de4c:oak_tdx_guest/src/lib.rs
=======
<<<<<<<< HEAD:oak_remote_attestation/src/lib.rs
#![no_std]

extern crate alloc;

pub mod proto {
    pub mod oak {
        pub mod session {
            pub mod v1 {
                #![allow(dead_code)]
                include!(concat!(env!("OUT_DIR"), "/oak.session.v1.rs"));
            }
        }
    }
}

pub mod attester;
pub mod handler;
#[cfg(test)]
mod tests;
pub mod verifier;
========
fn main() -> Result<(), Box<dyn std::error::Error>> {
    micro_rpc_build::compile(&["proto/v1/messages.proto"], &["proto/v1"]);

    Ok(())
}
>>>>>>>> 2fb4fa7785c93ccaf9a972be96d4ad5faa15de4c:oak_remote_attestation/build.rs
>>>>>>> 2fb4fa7785c93ccaf9a972be96d4ad5faa15de4c
