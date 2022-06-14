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

use crate::remote_attestation::AttestationHandler;
use alloc::vec::Vec;
use anyhow::Context;
use ciborium_io::{Read, Write};
use oak_baremetal_communication_channel::{schema, schema::TrustedRuntime, InvocationChannel};
use oak_idl::Handler;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, AttestationGenerator, AttestationVerifier,
};
use oak_remote_attestation_sessions::SessionId;

struct InvocationHandler<F, G, V>
where
    F: Send + Sync + Clone + FnOnce(Vec<u8>) -> anyhow::Result<Vec<u8>>,
    G: AttestationGenerator,
    V: AttestationVerifier,
{
    attestation_handler: AttestationHandler<F, G, V>,
}

impl<F, G, V> schema::TrustedRuntime for InvocationHandler<F, G, V>
where
    F: Send + Sync + Clone + FnOnce(Vec<u8>) -> anyhow::Result<Vec<u8>>,
    G: AttestationGenerator,
    V: AttestationVerifier,
{
    fn handle_user_request(
        &mut self,
        request_message: &schema::UserRequest,
    ) -> Result<oak_idl::utils::Message<schema::UserRequestResponse>, oak_idl::Status> {
        let session_id: SessionId = request_message
            .session_id()
            .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?
            .value()
            .into();
        let request_body: &[u8] = request_message
            .body()
            .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?;

        let response = self
            .attestation_handler
            .message(session_id, request_body)
            .map_err(|_| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;

        let response_message = {
            let mut builder = oak_idl::utils::MessageBuilder::default();
            let body = builder.create_vector::<u8>(&response);
            let user_request_response = schema::UserRequestResponse::create(
                &mut builder,
                &schema::UserRequestResponseArgs { body: Some(body) },
            );
            builder
                .finish(user_request_response)
                .map_err(|_| oak_idl::Status::new(oak_idl::StatusCode::Internal))?
        };
        Ok(response_message)
    }
}

// Processes incoming frames.
pub fn handle_frames<T, G: AttestationGenerator, V: AttestationVerifier>(
    channel: T,
    attestation_behavior: AttestationBehavior<G, V>,
) -> anyhow::Result<!>
where
    T: Read<Error = anyhow::Error> + Write<Error = anyhow::Error>,
{
    let wasm_handler = crate::wasm::new_wasm_handler()?;
    let attestation_handler = AttestationHandler::create(
        move |v| wasm_handler.handle_raw_invoke(v),
        attestation_behavior,
    );
    let mut invocation_handler = InvocationHandler {
        attestation_handler,
    }
    .serve();
    let invocation_channel = &mut InvocationChannel::new(channel);
    loop {
        let message = invocation_channel
            .read_message()
            .context("couldn't receive message")?;
        let response = invocation_handler.invoke((&message).into());
        invocation_channel.write_message(response.into())?
    }
}
