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
    remote_attestation::{AttestationHandler, AttestationSessionHandler},
    wasm,
};
use alloc::boxed::Box;
use anyhow::Context;
use ciborium_io::{Read, Write};
use oak_baremetal_communication_channel::{schema, schema::TrustedRuntime, InvocationChannel};
use oak_idl::Handler;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, AttestationGenerator, AttestationVerifier,
};
use oak_remote_attestation_sessions::SessionId;

enum InitializationState<G, V>
where
    G: AttestationGenerator,
    V: AttestationVerifier,
{
    Uninitialized(Option<AttestationBehavior<G, V>>),
    Initialized(Box<dyn AttestationHandler>),
}

struct InvocationHandler<G, V>
where
    G: AttestationGenerator,
    V: AttestationVerifier,
{
    initialization_state: InitializationState<G, V>,
}

impl<G: 'static, V: 'static> schema::TrustedRuntime for InvocationHandler<G, V>
where
    G: AttestationGenerator,
    V: AttestationVerifier,
{
    fn initialize(
        &mut self,
        initialization: &schema::Initialization,
    ) -> Result<
        oak_idl::utils::Message<oak_baremetal_communication_channel::schema::Empty>,
        oak_idl::Status,
    > {
        match &mut self.initialization_state {
            InitializationState::Initialized(_attestation_handler) => Err(oak_idl::Status::new(
                oak_idl::StatusCode::FailedPrecondition,
            )),
            InitializationState::Uninitialized(attestation_behavior) => {
                let attestation_behavior = attestation_behavior
                    .take()
                    .expect("The attestation_behavior should always be present. It is wrapped in an option purely so it can be taken without cloning.");
                let wasm_module_bytes: &[u8] = initialization
                    .wasm_module()
                    .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?;
                let wasm_handler = wasm::new_wasm_handler(wasm_module_bytes)
                    .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;
                let attestation_handler = Box::new(AttestationSessionHandler::create(
                    move |v| wasm_handler.handle_raw_invoke(v),
                    attestation_behavior,
                ));
                self.initialization_state = InitializationState::Initialized(attestation_handler);
                let response_message = {
                    let mut builder = oak_idl::utils::MessageBuilder::default();
                    let user_request_response =
                        schema::Empty::create(&mut builder, &schema::EmptyArgs {});
                    builder
                        .finish(user_request_response)
                        .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?
                };
                Ok(response_message)
            }
        }
    }

    fn handle_user_request(
        &mut self,
        request_message: &schema::UserRequest,
    ) -> Result<oak_idl::utils::Message<schema::UserRequestResponse>, oak_idl::Status> {
        match &mut self.initialization_state {
            InitializationState::Uninitialized(_attestation_behavior) => Err(oak_idl::Status::new(
                oak_idl::StatusCode::FailedPrecondition,
            )),
            InitializationState::Initialized(attestation_handler) => {
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
                    .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;

                let response_message = {
                    let mut builder = oak_idl::utils::MessageBuilder::default();
                    let body = builder.create_vector::<u8>(&response);
                    let user_request_response = schema::UserRequestResponse::create(
                        &mut builder,
                        &schema::UserRequestResponseArgs { body: Some(body) },
                    );
                    builder
                        .finish(user_request_response)
                        .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?
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
        initialization_state: InitializationState::Uninitialized(Some(attestation_behavior)),
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
