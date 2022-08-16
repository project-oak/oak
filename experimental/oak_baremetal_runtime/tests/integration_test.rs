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
// Permit unused variables as rust errounously complains about variables used
// only in assert_matches being unused. This cannot be set per line for each
// macro invocation.
#![allow(unused_variables)]

use core::assert_matches::assert_matches;
use oak_baremetal_runtime::{schema::TrustedRuntime, RuntimeImplementation};
use oak_remote_attestation::handshaker::{
    AttestationBehavior, ClientHandshaker, EmptyAttestationVerifier,
};
use oak_remote_attestation_amd::PlaceholderAmdAttestationGenerator;

mod schema {
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/schema_services_clients.rs"));
}

const MOCK_SESSION_ID: &[u8; 8] = &[0, 0, 0, 0, 0, 0, 0, 0];
const MOCK_CONSTANT_RESPONSE_SIZE: u32 = 1024;
const ECHO_WASM_BYTES: &[u8] = include_bytes!("echo.wasm");

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

    let expected_err = oak_idl::Status::new(oak_idl::StatusCode::FailedPrecondition);

    assert_matches!(result, Err(expected_err));
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

    let expected_err = oak_idl::Status::new(oak_idl::StatusCode::FailedPrecondition);
    assert_matches!(result, Err(_expected_err));
}
