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
use prost::Message;
use proto::oak::sandbox::runtime::{Request, Response};
use ringbuf::{Consumer, Producer, RingBuffer};
use std::{
    io::{Read, Write},
    os::unix::io::FromRawFd,
};
use vsock::VsockStream;

const FILE_DESCRIPTOR: c_int = 1023;
const BUFFER_SIZE: usize = 1024;

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
    read_buffer_producer: Producer<u8>,
    read_buffer_consumer: Consumer<u8>,
    // write_buffer_producer: Producer<u8>,
    // write_buffer_consumer: Consumer<u8>,
}

impl Channel {
    fn create(file_descriptor: c_int) -> anyhow::Result<Self> {
        let stream = unsafe { VsockStream::from_raw_fd(file_descriptor) };
        info!(
            "Connected to the {}",
            stream.peer_addr().map_err(|error| anyhow!("Couldn't get peer address: {:?}", error))?
        );

        let read_buffer = RingBuffer::<u8>::new(BUFFER_SIZE);
        let (read_buffer_producer, read_buffer_consumer) = read_buffer.split();

        // let write_buffer = RingBuffer::<u8>::new(BUFFER_SIZE);
        // let (write_buffer_producer, write_buffer_consumer) = write_buffer.split();

        Ok(Self {
            stream,
            read_buffer_producer,
            read_buffer_consumer,
            // write_buffer_producer,
            // write_buffer_consumer,
        })
    }
}

impl ciborium_io::Read for Channel {
    type Error = anyhow::Error;

    fn read_exact(&mut self, data: &mut [u8]) -> Result<(), Self::Error> {
        let mut buffer = vec![0; BUFFER_SIZE];
        let read_bytes = self.stream.read(&mut buffer).map_err(|error| anyhow!("Couldn't read from stream: {:?}", error))?;
        if read_bytes > 0 {
            let message = Request::decode(&buffer[..read_bytes])
                .map_err(|error| anyhow!("Couldn't decode proto message: {:?}", error))?;
            self.read_buffer_producer.push_slice(message.data.as_bytes());
        }

        self.read_buffer_consumer.read_exact(data).map_err(|error| anyhow!("Couldn't read from buffer: {:?}", error))
        // self.stream.read_exact(data).map_err(|error| anyhow!("Couldn't read from stream: {:?}", error))
    }
}

impl ciborium_io::Write for Channel {
    type Error = anyhow::Error;

    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        let message = Response {
            data: String::from_utf8(data.to_vec()).unwrap(),
        };
        let mut encoded_message = vec![];
        message.encode(&mut encoded_message)
            .map_err(|error| anyhow!("Couldn't encode proto message: {:?}", error))?;

        self.stream.write_all(data).map_err(|error| anyhow!("Couldn't write into stream: {:?}", error))
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        self.stream.flush().map_err(|error| anyhow!("Couldn't flush stream: {:?}", error))
    }
}
