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

use crate::{
    remote_attestation::AttestationHandler, Channel, Frame, FrameLength, FRAME_LENGTH_BYTES_SIZE,
};
use alloc::{vec, vec::Vec};
use anyhow::Context;

fn read_frame_from_channel(channel: &mut dyn Channel) -> anyhow::Result<Frame> {
    let mut length_buf = [0; FRAME_LENGTH_BYTES_SIZE];
    channel.recv(&mut length_buf)?;
    let length = FrameLength::from_be_bytes(length_buf);
    let mut body: Vec<u8> = vec![0; length.into()];
    channel.recv(&mut body)?;
    Ok(Frame { body })
}
// Processes incoming frames.
pub fn handle_frames(channel: &mut dyn Channel) -> anyhow::Result<!> {
    let wasm_handler = crate::wasm::new_wasm_handler()?;
    let attestation_handler =
        &mut AttestationHandler::create(move |v| wasm_handler.handle_raw_invoke(v));
    loop {
        let frame = read_frame_from_channel(channel).context("couldn't receive message")?;
        let response = attestation_handler
            .message(frame.body)
            .context("attestation failed")?;

        let encoded_response = Frame { body: response }
            .encode()
            .context("couldn't encode response")?;
        channel
            .send(&encoded_response)
            .context("couldn't send response")?;
    }
}
