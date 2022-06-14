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

// pub mod proto {
//     #![allow(clippy::return_self_not_must_use)]
//     tonic::include_proto!("oak.sandbox.runtime");
// }

pub mod proto {
    pub mod oak {
        pub mod sandbox {
            pub mod runtime {
                include!(concat!(
                    env!("OUT_DIR"),
                    "/oak.sandbox.runtime.rs"
                ));
            }
        }
    }
}

use anyhow::anyhow;
use libc::c_int;
use log::info;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, EmptyAttestationGenerator, EmptyAttestationVerifier,
};
use proto::oak::sandbox::runtime::{Request, Response};
use std::{
    io::{Read, Write},
    os::unix::io::FromRawFd,
};
use vsock::VsockStream;

const FILE_DESCRIPTOR: c_int = 1023;

fn main() {
    let attestation_behavior =
        AttestationBehavior::create(EmptyAttestationGenerator, EmptyAttestationVerifier);
    oak_baremetal_runtime::framing::handle_frames(
        Channel::create(FILE_DESCRIPTOR).expect("Couldn't create channel"),
        attestation_behavior
    ).expect("Couldn't handle frames");
}

struct Channel {
    stream: VsockStream,
}

impl Channel {
    fn create(file_descriptor: c_int) -> anyhow::Result<Self> {
        let stream = unsafe { VsockStream::from_raw_fd(file_descriptor) };
        info!(
            "Connected to the {}",
            stream.peer_addr().map_err(|error| anyhow!("Couldn't get peer address: {:?}", error))?
        );
        Ok(Self { stream })
    }
}

impl ciborium_io::Read for Channel {
    type Error = anyhow::Error;

    fn read_exact(&mut self, data: &mut [u8]) -> Result<(), Self::Error> {
        self.stream.read_exact(data).map_err(|error| anyhow!("Couldn't read from stream: {:?}", error))
    }
}

impl ciborium_io::Write for Channel {
    type Error = anyhow::Error;

    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        self.stream.write_all(data).map_err(|error| anyhow!("Couldn't write into stream: {:?}", error))
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        self.stream.flush().map_err(|error| anyhow!("Couldn't flush stream: {:?}", error))
    }
}
