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
    remote_attestation::{AttestationHandler, AttestationTrait},
    wasm,
};
use alloc::boxed::Box;
use anyhow::Context;
use channel::{schema, schema::TrustedRuntime, Framed};
use ciborium_io::{Read, Write};
use oak_idl::Handler;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, AttestationGenerator, AttestationVerifier,
};
use oak_remote_attestation_sessions::SessionId;

enum AttestationState<G, V>
where
    G: AttestationGenerator,
    V: AttestationVerifier,
{
    Uninitialized(AttestationBehavior<G, V>),
    Initialized(Box<dyn AttestationTrait>),
}

struct InvocationHandler<G, V>
where
    G: AttestationGenerator,
    V: AttestationVerifier,
{
    attestation_state: AttestationState<G, V>,
}

impl<G: 'static, V: 'static> schema::TrustedRuntime for InvocationHandler<G, V>
where
    G: AttestationGenerator,
    V: AttestationVerifier,
{
    fn initialize(
        &mut self,
        initialization: &schema::Initialization,
    ) -> Result<oak_idl::utils::Message<channel::schema::Empty>, oak_idl::Status> {
        match &mut self.attestation_state {
            AttestationState::Initialized(_attestation_handler) => Err(oak_idl::Status::new(
                oak_idl::StatusCode::FailedPrecondition,
            )),
            AttestationState::Uninitialized(attestation_behavior) => {
                let wasm_module_bytes: &[u8] = initialization
                    .wasm_module()
                    .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?;
                let wasm_handler = wasm::new_wasm_handler(wasm_module_bytes)
                    .map_err(|_| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;
                let attestation_handler = Box::new(AttestationHandler::create(
                    move |v| wasm_handler.handle_raw_invoke(v),
                    attestation_behavior.clone(),
                ));
                self.attestation_state = AttestationState::Initialized(attestation_handler);
                let response_message = {
                    let mut builder = oak_idl::utils::MessageBuilder::default();
                    let user_request_response =
                        schema::Empty::create(&mut builder, &schema::EmptyArgs {});
                    builder
                        .finish(user_request_response)
                        .map_err(|_| oak_idl::Status::new(oak_idl::StatusCode::Internal))?
                };
                Ok(response_message)
            }
        }
    }

    fn handle_user_request(
        &mut self,
        request_message: &schema::UserRequest,
    ) -> Result<oak_idl::utils::Message<schema::UserRequestResponse>, oak_idl::Status> {
        match &mut self.attestation_state {
            AttestationState::Uninitialized(_attestation_behavior) => Err(oak_idl::Status::new(
                oak_idl::StatusCode::FailedPrecondition,
            )),
            AttestationState::Initialized(attestation_handler) => {
                let session_id: SessionId = request_message
                    .session_id()
                    .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?
                    .value()
                    .into();
                let request_body: &[u8] = request_message
                    .body()
                    .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?;

                let response = attestation_handler
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
    }
}

// Processes incoming frames.
pub fn handle_frames<T, G: 'static + AttestationGenerator, V: 'static + AttestationVerifier>(
    channel: T,
    attestation_behavior: AttestationBehavior<G, V>,
) -> anyhow::Result<!>
where
    T: Read<Error = anyhow::Error> + Write<Error = anyhow::Error>,
{
    let mut invocation_handler = InvocationHandler {
        attestation_state: AttestationState::Uninitialized(attestation_behavior),
    }
    .serve();
    let framed = &mut Framed::new(channel);
    loop {
        let frame = framed.read_frame().context("couldn't receive message")?;
        let response = invocation_handler.invoke((&frame).into());
        framed.write_frame(response.into())?
    }
}
