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
    logger::StandaloneLogger,
    remote_attestation::{AttestationHandler, AttestationSessionHandler},
    wasm,
};
use alloc::{boxed::Box, sync::Arc};
use anyhow::Context;
use oak_baremetal_communication_channel::{
    schema,
    schema::TrustedRuntime,
    server::{message_from_response_and_id, ServerChannelHandle},
    Channel,
};
use oak_functions_abi::Request;
use oak_functions_lookup::LookupDataManager;
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
    // dyn is used as our attestation implementation uses a closure, which is
    // created only at initialization time. We cannot know the closure
    // type in advance, since Rust closures have unique, anonymous types.
    Initialized(Box<dyn AttestationHandler>),
}

struct InvocationHandler<G, V>
where
    G: AttestationGenerator,
    V: AttestationVerifier,
{
    initialization_state: InitializationState<G, V>,
    lookup_data_manager: Arc<LookupDataManager<StandaloneLogger>>,
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

                let wasm_handler =
                    wasm::new_wasm_handler(wasm_module_bytes, self.lookup_data_manager.clone())
                        .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;
                let attestation_handler = Box::new(AttestationSessionHandler::create(
                    move |decrypted_request| {
                        wasm_handler
                            .handle_invoke(Request {
                                body: decrypted_request,
                            })
                            .map(|decrypted_response| decrypted_response.encode_to_vec())
                    },
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

    fn update_lookup_data(
        &mut self,
        lookup_data: &schema::LookupData,
    ) -> Result<
        oak_idl::utils::Message<oak_baremetal_communication_channel::schema::Empty>,
        oak_idl::Status,
    > {
        let data = lookup_data
            .items()
            .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?
            .iter()
            .map(|entry| {
                Ok((
                    entry
                        .key()
                        .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?
                        .to_vec(),
                    entry
                        .value()
                        .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?
                        .to_vec(),
                ))
            })
            .collect::<Result<_, oak_idl::Status>>()?;

        self.lookup_data_manager.update_data(data);
        let response_message = {
            let mut builder = oak_idl::utils::MessageBuilder::default();
            let user_request_response = schema::Empty::create(&mut builder, &schema::EmptyArgs {});
            builder
                .finish(user_request_response)
                .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?
        };
        Ok(response_message)
    }
}

// Processes incoming frames.
pub fn handle_frames<G: 'static + AttestationGenerator, V: 'static + AttestationVerifier>(
    channel: Box<dyn Channel>,
    attestation_behavior: AttestationBehavior<G, V>,
) -> anyhow::Result<!> {
    let mut invocation_handler = InvocationHandler {
        initialization_state: InitializationState::Uninitialized(Some(attestation_behavior)),
        lookup_data_manager: Arc::new(LookupDataManager::new_empty(StandaloneLogger::default())),
    }
    .serve();
    let channel_handle = &mut ServerChannelHandle::new(channel);
    loop {
        let request_message = channel_handle
            .read_request()
            .context("couldn't receive message")?;
        let request_message_invocation_id = request_message.invocation_id;
        let response = invocation_handler.invoke(request_message.into());
        // For now all messages are sent in sequence, hence the id of the next
        // response always matches that of the preceeding request.
        // TODO(#2848): Allow messages to be sent and received out of order.
        let response_message =
            message_from_response_and_id(response, request_message_invocation_id);
        channel_handle.write_response(response_message)?
    }
}
