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

#![no_std]
#![feature(never_type)]

extern crate alloc;

pub mod schema {
    #![allow(dead_code)]
    use prost::Message;
    include!(concat!(env!("OUT_DIR"), "/oak.functions.rs"));
}
mod logger;
mod remote_attestation;
mod wasm;

use crate::remote_attestation::{AttestationHandler, AttestationSessionHandler};
use alloc::{boxed::Box, format, sync::Arc};
use anyhow::Context;
use oak_functions_abi::Request;
use oak_functions_lookup::LookupDataManager;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, AttestationGenerator, AttestationVerifier,
};
use oak_remote_attestation_sessions::SessionId;

pub use crate::logger::StandaloneLogger;

enum InitializationState<G, V>
where
    G: 'static + AttestationGenerator,
    V: 'static + AttestationVerifier,
{
    Uninitialized(Option<AttestationBehavior<G, V>>),
    // dyn is used as our attestation implementation uses a closure, which is
    // created only at initialization time. We cannot know the closure
    // type in advance, since Rust closures have unique, anonymous types.
    Initialized(Box<dyn AttestationHandler>),
}

pub struct RuntimeImplementation<G, V>
where
    G: 'static + AttestationGenerator,
    V: 'static + AttestationVerifier,
{
    initialization_state: InitializationState<G, V>,
    lookup_data_manager: Arc<LookupDataManager<logger::StandaloneLogger>>,
}

impl<G, V> RuntimeImplementation<G, V>
where
    G: 'static + AttestationGenerator,
    V: 'static + AttestationVerifier,
{
    pub fn new(attestation_behavior: AttestationBehavior<G, V>) -> Self {
        Self {
            initialization_state: InitializationState::Uninitialized(Some(attestation_behavior)),
            lookup_data_manager: Arc::new(
                LookupDataManager::new_empty(StandaloneLogger::default()),
            ),
        }
    }
}

impl<G, V> schema::TrustedRuntime for RuntimeImplementation<G, V>
where
    G: 'static + AttestationGenerator,
    V: 'static + AttestationVerifier,
{
    fn initialize(
        &mut self,
        initialization: &schema::Initialization,
    ) -> Result<schema::InitializeResponse, oak_idl::Status> {
        match &mut self.initialization_state {
            InitializationState::Initialized(_attestation_handler) => {
                Err(oak_idl::Status::new_with_message(
                    oak_idl::StatusCode::FailedPrecondition,
                    "already initialized",
                ))
            }
            InitializationState::Uninitialized(attestation_behavior) => {
                // attestation_behavior must always be present; it is wrapped in an Option purely so
                // that it can be taken without cloning.
                let attestation_behavior = attestation_behavior.take().ok_or_else(|| {
                    oak_idl::Status::new_with_message(
                        oak_idl::StatusCode::Internal,
                        "missing attestation_behavior",
                    )
                })?;
                let constant_response_size = initialization.constant_response_size;
                let wasm_handler = wasm::new_wasm_handler(
                    &initialization.wasm_module,
                    self.lookup_data_manager.clone(),
                )
                .map_err(|err| {
                    oak_idl::Status::new_with_message(
                        oak_idl::StatusCode::Internal,
                        format!("could not initialize Wasm handler: {:?}", err),
                    )
                })?;
                let attestation_handler = Box::new(
                    AttestationSessionHandler::create(
                        move |decrypted_request| {
                            let decrypted_response = wasm_handler.handle_invoke(Request {
                                body: decrypted_request,
                            })?;

                            let padded_decrypted_response =
                                decrypted_response
                                    .pad(constant_response_size.try_into().expect(
                                        "failed to convert constant_response_size to usize",
                                    ))
                                    .context("could not pad the response")?;

                            Ok(padded_decrypted_response.encode_to_vec())
                        },
                        attestation_behavior,
                    )
                    .map_err(|err| {
                        oak_idl::Status::new_with_message(
                            oak_idl::StatusCode::Internal,
                            format!("could not create attestation handler: {:?}", err),
                        )
                    })?,
                );
                let public_key_info = attestation_handler.get_public_key_info();
                self.initialization_state = InitializationState::Initialized(attestation_handler);
                Ok(schema::InitializeResponse {
                    public_key_info: Some(schema::PublicKeyInfo {
                        public_key: public_key_info.public_key,
                        attestation: public_key_info.attestation,
                    }),
                })
            }
        }
    }

    fn handle_user_request(
        &mut self,
        request_message: &schema::UserRequest,
    ) -> Result<schema::UserRequestResponse, oak_idl::Status> {
        match &mut self.initialization_state {
            InitializationState::Uninitialized(_attestation_behavior) => {
                Err(oak_idl::Status::new_with_message(
                    oak_idl::StatusCode::FailedPrecondition,
                    "not initialized",
                ))
            }
            InitializationState::Initialized(attestation_handler) => {
                let session_id: SessionId = request_message
                    .session_id
                    .clone()
                    .ok_or_else(|| {
                        oak_idl::Status::new_with_message(
                            oak_idl::StatusCode::InvalidArgument,
                            "missing session_id",
                        )
                    })?
                    .value
                    .try_into()
                    .map_err(|err| {
                        oak_idl::Status::new_with_message(
                            oak_idl::StatusCode::InvalidArgument,
                            format!("could not parse session_id: {:?}", err),
                        )
                    })?;

                let response = attestation_handler
                    .message(session_id, &request_message.body)
                    .map_err(|err| {
                        oak_idl::Status::new_with_message(
                            oak_idl::StatusCode::Internal,
                            format!("{:?}", err),
                        )
                    })?;

                Ok(schema::UserRequestResponse { body: response })
            }
        }
    }

    fn update_lookup_data(
        &mut self,
        lookup_data: &schema::LookupData,
    ) -> Result<schema::Empty, oak_idl::Status> {
        let data = lookup_data
            .items
            .iter()
            .map(|entry| Ok((entry.key.clone(), entry.value.clone())))
            .collect::<Result<_, oak_idl::Status>>()?;

        self.lookup_data_manager.update_data(data);
        Ok(schema::Empty {})
    }
}
