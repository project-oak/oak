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

use crate::{remote_attestation::AttestationHandler, Frame, Framed};
use anyhow::Context;

// Processes incoming frames.
pub fn handle_frames<T>(channel: T) -> anyhow::Result<!>
where
    T: core2::io::Read + core2::io::Write,
{
    let wasm_handler = crate::wasm::new_wasm_handler()?;
    let attestation_handler =
        &mut AttestationHandler::create(move |v| wasm_handler.handle_raw_invoke(v));
    let framed = &mut Framed::new(channel);
    loop {
        let frame = framed.read_frame().context("couldn't receive message")?;
        let response = attestation_handler
            .message(frame.body)
            .context("attestation failed")?;
        let reponse_frame = Frame { body: response };
        framed.write_frame(reponse_frame)?
    }
}
