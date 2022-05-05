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

use crate::{remote_attestation::AttestationHandler, Channel, SerializedRequest};
use anyhow::Context;
use ciborium::{de, ser};

impl ciborium_io::Write for &mut dyn Channel {
    type Error = anyhow::Error;

    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        self.send(data)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl ciborium_io::Read for &mut dyn Channel {
    type Error = anyhow::Error;

    fn read_exact(&mut self, data: &mut [u8]) -> Result<(), Self::Error> {
        self.recv(data)
    }
}

// Processes incoming frames.
pub fn handle_frames(mut channel: &mut dyn Channel) -> anyhow::Result<!> {
    let wasm_handler = crate::wasm::new_wasm_handler()?;
    let attestation_handler =
        &mut AttestationHandler::create(move |v| wasm_handler.handle_raw_invoke(v));
    loop {
        let serialized_request: SerializedRequest = de::from_reader(&mut channel)
            .map_err(anyhow::Error::msg)
            .context("couldn't deserialize message")?;
        let response = attestation_handler
            .message(serialized_request)
            .context("attestation failed")?;
        ser::into_writer(&response, &mut channel)
            .map_err(anyhow::Error::msg)
            .context("couldn't serialize response")?;
    }
}
