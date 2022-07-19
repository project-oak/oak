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

#![feature(cursor_remaining)]

pub mod proto {
    pub mod oak {
        pub mod sandbox {
            pub mod runtime {
                include!(concat!(env!("OUT_DIR"), "/oak.sandbox.runtime.rs"));
            }
        }
    }
}
pub mod channel;

use crate::channel::Channel;
use libc::c_int;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, EmptyAttestationGenerator, EmptyAttestationVerifier,
};

const FILE_DESCRIPTOR: c_int = 1023;

fn main() {
    let attestation_behavior =
        AttestationBehavior::create(EmptyAttestationGenerator, EmptyAttestationVerifier);
    oak_baremetal_runtime::framing::handle_frames(
        Box::new(Channel::create(FILE_DESCRIPTOR).expect("Couldn't create channel")),
        attestation_behavior,
    )
    .expect("Couldn't handle frames");
}
