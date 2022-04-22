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

extern crate alloc;

use crate::{remote_attestation::AttestationHandler, Channel};
use alloc::vec::Vec;
use ciborium::{de, ser};

#[derive(Debug)]
pub enum Error<T> {
    // An error occured while deserializing.
    Deserialization(ciborium::de::Error<T>),

    // An error occured while serializing.
    Serialization(ciborium::ser::Error<T>),

    // An error occured in remote attestation.
    Attestation(anyhow::Error),
}

impl<E> ciborium_io::Write for &mut dyn Channel<Error = E> {
    type Error = E;

    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        self.send(data)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl<E> ciborium_io::Read for &mut dyn Channel<Error = E> {
    type Error = E;

    fn read_exact(&mut self, data: &mut [u8]) -> Result<(), Self::Error> {
        self.recv(data)
    }
}

const MOCK_SESSION_ID: [u8; 8] = [0; 8];

// Echoes all input on the interface back out.
pub fn echo<E: core::fmt::Debug>(mut channel: &mut dyn Channel<Error = E>) -> Result<!, Error<E>> {
    let attestation_handler = &mut AttestationHandler::create(|v| v);
    loop {
        let msg: Vec<u8> = de::from_reader(&mut channel).map_err(Error::Deserialization)?;
        let response = attestation_handler
            .message(MOCK_SESSION_ID, msg)
            .map_err(Error::Attestation)?;
        ser::into_writer(&response, &mut channel).map_err(Error::Serialization)?;
    }
}
