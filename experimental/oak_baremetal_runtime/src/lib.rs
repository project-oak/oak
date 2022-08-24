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
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/schema_services_servers.rs"));
}
mod logger;
mod remote_attestation;
mod wasm;

use crate::{
    logger::StandaloneLogger,
    remote_attestation::{AttestationHandler, AttestationSessionHandler},
};
use alloc::{boxed::Box, sync::Arc};
use anyhow::Context;
use oak_functions_abi::Request;
use oak_functions_lookup::LookupDataManager;
use oak_remote_attestation::handshaker::{
    AttestationBehavior, AttestationGenerator, AttestationVerifier,
};
use oak_remote_attestation_sessions::SessionId;

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
    ) -> Result<oak_idl::utils::OwnedFlatbuffer<crate::schema::Empty>, oak_idl::Status> {
        match &mut self.initialization_state {
            InitializationState::Initialized(_attestation_handler) => Err(oak_idl::Status::new(
                oak_idl::StatusCode::FailedPrecondition,
            )),
            InitializationState::Uninitialized(attestation_behavior) => {
                let attestation_behavior = attestation_behavior
                    .take()
                    .expect("The attestation_behavior should always be present. It is wrapped in an option purely so it can be taken without cloning.");
                let constant_response_size = initialization.constant_response_size();
                let wasm_module_bytes: &[u8] = initialization
                    .wasm_module()
                    .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?;

                let wasm_handler =
                    wasm::new_wasm_handler(wasm_module_bytes, self.lookup_data_manager.clone())
                        .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;
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
                    .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?,
                );
                self.initialization_state = InitializationState::Initialized(attestation_handler);
                let response_message = {
                    let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
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
    ) -> Result<oak_idl::utils::OwnedFlatbuffer<schema::UserRequestResponse>, oak_idl::Status> {
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
                    let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
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
    ) -> Result<oak_idl::utils::OwnedFlatbuffer<crate::schema::Empty>, oak_idl::Status> {
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
            let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
            let user_request_response = schema::Empty::create(&mut builder, &schema::EmptyArgs {});
            builder
                .finish(user_request_response)
                .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?
        };
        Ok(response_message)
    }
}
