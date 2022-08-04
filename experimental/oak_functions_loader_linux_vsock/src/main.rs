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

#[cfg(test)]
mod tests;

use crate::channel::Channel;
use clap::Parser;
use log::info;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, EmptyAttestationGenerator, EmptyAttestationVerifier,
};
use std::os::unix::{io::FromRawFd, prelude::RawFd};
use vsock::VsockStream;

#[derive(Parser, Clone, Debug)]
#[clap(about = "Oak Functions Loader Linux VSock")]
pub struct Opt {
    #[clap(
        long,
        default_value = "1023",
        help = "File descriptor to use for the communication channel"
    )]
    pub file_descriptor: i32,
}

// Connect to the file descriptor created by Bedebox using vsock.
pub fn create_vsock_stream(file_descriptor: RawFd) -> anyhow::Result<VsockStream> {
    let stream = unsafe { VsockStream::from_raw_fd(file_descriptor) };
    Ok(stream)
}

fn main() -> ! {
    let opt = Opt::parse();

    let stream = create_vsock_stream(opt.file_descriptor).expect("Couldn't create channel");
    info!(
        "Connected to the {}",
        stream.peer_addr().expect("Couldn't get peer address")
    );

    let attestation_behavior =
        AttestationBehavior::create(EmptyAttestationGenerator, EmptyAttestationVerifier);
    let channel = Box::new(Channel::new(stream));
    oak_baremetal_runtime::start(channel, attestation_behavior)
        .expect("Runtime encountered an unrecoverable error");
}
