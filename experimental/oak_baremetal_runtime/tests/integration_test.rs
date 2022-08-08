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

#![feature(assert_matches)]

extern crate alloc;

use core::assert_matches::assert_matches;
use oak_baremetal_runtime::{
    schema::{TrustedRuntime, TrustedRuntimeServer},
    RuntimeImplementation,
};
use oak_remote_attestation::handshaker::{
    AttestationBehavior, ClientHandshaker, EmptyAttestationVerifier,
};
use oak_remote_attestation_amd::PlaceholderAmdAttestationGenerator;
use oak_remote_attestation_sessions_client::UnaryClient;

mod schema {
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/schema_services_clients.rs"));
}

const MOCK_SESSION_ID: &[u8; 8] = &[0, 0, 0, 0, 0, 0, 0, 0];
const MOCK_CONSTANT_RESPONSE_SIZE: u32 = 1024;
const ECHO_WASM_BYTES: &[u8] = include_bytes!("echo.wasm");

// The type of the client used to interact with the runtime in integration tests
type RuntimeClient = schema::TrustedRuntimeClient<
    TrustedRuntimeServer<
        RuntimeImplementation<PlaceholderAmdAttestationGenerator, EmptyAttestationVerifier>,
    >,
>;

/// Simple test client to perform handshakes with the runtime over several user requests. Allows
/// the subsequent exchange of user data, and testing of the Wasm business logic running in the
/// runtime.
struct TestUserClient {
    inner: alloc::rc::Rc<core::cell::RefCell<RuntimeClient>>,
}

#[async_trait::async_trait(?Send)]
impl UnaryClient for TestUserClient {
    async fn message(
        &mut self,
        session_id: oak_remote_attestation_sessions::SessionId,
        body: Vec<u8>,
    ) -> anyhow::Result<Vec<u8>> {
        let owned_request_flatbuffer = {
            let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
            let session_id = &schema::SessionId::new(&session_id);
            let body = builder.create_vector::<u8>(&body);
            let flatbuffer = schema::UserRequest::create(
                &mut builder,
                &schema::UserRequestArgs {
                    session_id: Some(session_id),
                    body: Some(body),
                },
            );
            builder
                .finish(flatbuffer)
                .map_err(|err| {
                    oak_idl::Status::new_with_message(
                        oak_idl::StatusCode::Internal,
                        err.to_string(),
                    )
                })
                .unwrap()
        };
        let mut mutinner = self.inner.borrow_mut();
        let response_flatbuffer = mutinner
            .handle_user_request(owned_request_flatbuffer.into_vec())
            .unwrap();

        let decoded_response = response_flatbuffer.get().body().unwrap();

        Ok(decoded_response.to_vec())
    }
}

#[test]
fn it_should_not_handle_user_requests_before_initialization() {
    let attestation_behavior =
        AttestationBehavior::create(PlaceholderAmdAttestationGenerator, EmptyAttestationVerifier);
    let runtime = RuntimeImplementation::new(attestation_behavior.clone());
    let mut client = schema::TrustedRuntimeClient::new(TrustedRuntime::serve(runtime));

    let mut handshaker =
        ClientHandshaker::new(attestation_behavior).expect("could not create client handshaker");
    let client_hello = handshaker
        .create_client_hello()
        .expect("Couldn't create client hello message");

    let owned_request_flatbuffer = {
        let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let session_id = &schema::SessionId::new(MOCK_SESSION_ID);
        let body = builder.create_vector::<u8>(&client_hello);
        let flatbuffer = schema::UserRequest::create(
            &mut builder,
            &schema::UserRequestArgs {
                session_id: Some(session_id),
                body: Some(body),
            },
        );
        builder
            .finish(flatbuffer)
            .map_err(|err| {
                oak_idl::Status::new_with_message(oak_idl::StatusCode::Internal, err.to_string())
            })
            .unwrap()
    };
    let result = client.handle_user_request(owned_request_flatbuffer.into_vec());

    assert_matches!(
        result,
        Err(oak_idl::Status {
            code: oak_idl::StatusCode::FailedPrecondition,
            ..
        })
    );
}

#[test]
fn it_should_handle_user_requests_after_initialization() {
    let attestation_behavior =
        AttestationBehavior::create(PlaceholderAmdAttestationGenerator, EmptyAttestationVerifier);
    let runtime = oak_baremetal_runtime::RuntimeImplementation::new(attestation_behavior.clone());
    let mut client = schema::TrustedRuntimeClient::new(TrustedRuntime::serve(runtime));

    let owned_initialization_flatbuffer = {
        let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let wasm_module = builder.create_vector::<u8>(ECHO_WASM_BYTES);
        let initialization_flatbuffer = schema::Initialization::create(
            &mut builder,
            &schema::InitializationArgs {
                wasm_module: Some(wasm_module),
                constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
            },
        );

        builder
            .finish(initialization_flatbuffer)
            .expect("errored when creating initialization message")
    };

    client
        .initialize(owned_initialization_flatbuffer.into_vec())
        .unwrap();

    let mut handshaker =
        ClientHandshaker::new(attestation_behavior).expect("could not create client handshaker");
    let client_hello = handshaker
        .create_client_hello()
        .expect("Couldn't create client hello message");

    let owned_request_flatbuffer = {
        let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let session_id = &schema::SessionId::new(MOCK_SESSION_ID);
        let body = builder.create_vector::<u8>(&client_hello);
        let flatbuffer = schema::UserRequest::create(
            &mut builder,
            &schema::UserRequestArgs {
                session_id: Some(session_id),
                body: Some(body),
            },
        );
        builder
            .finish(flatbuffer)
            .map_err(|err| {
                oak_idl::Status::new_with_message(oak_idl::StatusCode::Internal, err.to_string())
            })
            .unwrap()
    };
    let result = client.handle_user_request(owned_request_flatbuffer.into_vec());

    assert_matches!(result, Ok(_));
}

#[test]
fn it_should_only_initialize_once() {
    let attestation_behavior =
        AttestationBehavior::create(PlaceholderAmdAttestationGenerator, EmptyAttestationVerifier);
    let runtime = oak_baremetal_runtime::RuntimeImplementation::new(attestation_behavior);
    let mut client = schema::TrustedRuntimeClient::new(TrustedRuntime::serve(runtime));

    let owned_initialization_flatbuffer = {
        let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let wasm_module = builder.create_vector::<u8>(ECHO_WASM_BYTES);
        let initialization_flatbuffer = schema::Initialization::create(
            &mut builder,
            &schema::InitializationArgs {
                wasm_module: Some(wasm_module),
                constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
            },
        );

        builder
            .finish(initialization_flatbuffer)
            .expect("errored when creating initialization message")
    };

    let init_args = owned_initialization_flatbuffer.into_vec();

    client.initialize(init_args.clone()).unwrap();

    let result = client.initialize(init_args);

    assert_matches!(
        result,
        Err(oak_idl::Status {
            code: oak_idl::StatusCode::FailedPrecondition,
            ..
        })
    );
}
