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

use crate::proto::oak::sandbox::runtime::{Request, Response};
use anyhow::anyhow;
use prost::Message;
use ringbuf::{Consumer, Producer, RingBuffer};
use std::{
    io::{Read, Write},
    mem::size_of,
};

const BUFFER_SIZE: usize = 4000;

// Implements a Bedebox communication channel encoding in which every message is
// represented as a `length:value` where `value` is a Protobuf encoded message.
pub struct Channel<T>
where
    T: Read + Write,
{
    stream: T,
    read_buffer_producer: Producer<u8>,
    read_buffer_consumer: Consumer<u8>,
}

impl<T> Channel<T>
where
    T: Read + Write,
{
    pub fn new(stream: T) -> Self {
        let read_buffer = RingBuffer::<u8>::new(BUFFER_SIZE);
        let (read_buffer_producer, read_buffer_consumer) = read_buffer.split();

        Self {
            stream,
            read_buffer_producer,
            read_buffer_consumer,
        }
    }
}

impl<T> oak_baremetal_communication_channel::Read for Channel<T>
where
    T: std::io::Read + std::io::Write,
{
    fn read(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        while self.read_buffer_consumer.len() < data.len() {
            // Read message size.
            let mut size_buffer: [u8; size_of::<u64>()] = [0; size_of::<u64>()];
            self.stream.read(&mut size_buffer).map_err(|error| {
                anyhow!(
                    "Couldn't read Protobuf message size from stream: {:?}",
                    error
                )
            })?;
            let size = usize::from_ne_bytes(size_buffer);

            if size > 0 {
                // Read Protobuf message.
                let mut message_buffer: Vec<u8> = vec![0; size];
                self.stream.read(&mut message_buffer).map_err(|error| {
                    anyhow!(
                        "Couldn't read Protobuf message from stream: {:?}",
                        error
                    )
                })?;

                let message = Request::decode(&*message_buffer)
                    .map_err(|error| anyhow!("Couldn't decode Protobuf message: {:?}", error))?;
                self.read_buffer_producer.push_slice(&message.data);
            } else {
                return Err(anyhow!("Message size is 0"));
            }
        }

        self.read_buffer_consumer
            .read_exact(data)
            .map_err(|error| anyhow!("Couldn't read from buffer: {:?}", error))
    }
}

impl<T> oak_baremetal_communication_channel::Write for Channel<T>
where
    T: Read + Write,
{
    fn write(&mut self, data: &[u8]) -> anyhow::Result<()> {
        // Create Protobuf message.
        let message = Response {
            data: data.to_vec(),
        };
        let mut message_buffer = vec![];
        message
            .encode(&mut message_buffer)
            .map_err(|error| anyhow!("Couldn't encode proto message: {:?}", error))?;

        // Write Protobuf message size.
        let size_buffer: [u8; size_of::<u64>()] = (message_buffer.len() as u64).to_ne_bytes();
        self.stream
            .write_all(&size_buffer)
            .map_err(|error| anyhow!("Couldn't write into stream: {:?}", error))?;

        // Write Protobuf message.
        self.stream
            .write_all(&message_buffer)
            .map_err(|error| anyhow!("Couldn't write into stream: {:?}", error))
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        self.stream
            .flush()
            .map_err(|error| anyhow!("Couldn't flush stream: {:?}", error))
    }
}
