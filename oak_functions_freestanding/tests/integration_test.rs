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
#![feature(unwrap_infallible)]

extern crate alloc;

use core::assert_matches::assert_matches;
use oak_functions_freestanding::{
    schema,
    schema::{TrustedRuntime, TrustedRuntimeServer},
    RuntimeImplementation,
};
use oak_remote_attestation::handshaker::{
    AttestationBehavior, ClientHandshaker, EmptyAttestationGenerator, EmptyAttestationVerifier,
};
use oak_remote_attestation_amd::{
    PlaceholderAmdAttestationGenerator, PlaceholderAmdAttestationVerifier,
};
use oak_remote_attestation_sessions_client::{AttestationTransport, GenericAttestationClient};

const MOCK_SESSION_ID: &[u8; 8] = &[0, 0, 0, 0, 0, 0, 0, 0];
const MOCK_CONSTANT_RESPONSE_SIZE: u32 = 1024;
const LOOKUP_TEST_KEY: &[u8] = b"test_key";
const LOOKUP_TEST_VALUE: &[u8] = b"test_value";

/// Simple remote attestation client to perform handshakes with the runtime, which is a prerequisite
/// for interacting with the business logic running in the runtime.
struct TestUserClient {
    inner: schema::TrustedRuntimeClient<
        TrustedRuntimeServer<
            RuntimeImplementation<PlaceholderAmdAttestationGenerator, EmptyAttestationVerifier>,
        >,
    >,
}

#[async_trait::async_trait(?Send)]
impl AttestationTransport for TestUserClient {
    async fn message(
        &mut self,
        session_id: oak_remote_attestation_sessions::SessionId,
        body: Vec<u8>,
    ) -> anyhow::Result<Vec<u8>> {
        let request = schema::UserRequest {
            session_id: Some(schema::SessionId {
                value: session_id.to_vec(),
            }),
            body,
        };
        let response = self
            .inner
            .handle_user_request(&request)
            .unwrap()
            .map_err(|err| anyhow::anyhow!("could not handle user request: {:?}", err))?;
        Ok(response.body)
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
    let request = schema::UserRequest {
        session_id: Some(schema::SessionId {
            value: MOCK_SESSION_ID.to_vec(),
        }),
        body: client_hello,
    };
    let result = client.handle_user_request(&request).into_ok();

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
    let runtime = RuntimeImplementation::new(attestation_behavior.clone());
    let mut client = schema::TrustedRuntimeClient::new(TrustedRuntime::serve(runtime));

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("echo").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = schema::Initialization {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    client.initialize(&request).into_ok().unwrap();

    let mut handshaker =
        ClientHandshaker::new(attestation_behavior).expect("could not create client handshaker");
    let client_hello = handshaker
        .create_client_hello()
        .expect("Couldn't create client hello message");

    let request = schema::UserRequest {
        session_id: Some(schema::SessionId {
            value: MOCK_SESSION_ID.to_vec(),
        }),
        body: client_hello,
    };
    let result = client.handle_user_request(&request).into_ok();

    assert!(result.is_ok());
}

#[test]
fn it_should_only_initialize_once() {
    let attestation_behavior =
        AttestationBehavior::create(PlaceholderAmdAttestationGenerator, EmptyAttestationVerifier);
    let runtime = RuntimeImplementation::new(attestation_behavior);
    let mut client = schema::TrustedRuntimeClient::new(TrustedRuntime::serve(runtime));

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("echo").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = schema::Initialization {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };
    client.initialize(&request).into_ok().unwrap();

    let result = client.initialize(&request).into_ok();

    assert_matches!(
        result,
        Err(oak_idl::Status {
            code: oak_idl::StatusCode::FailedPrecondition,
            ..
        })
    );
}

#[tokio::test]
async fn it_should_support_lookup_data() {
    let attestation_behavior =
        AttestationBehavior::create(PlaceholderAmdAttestationGenerator, EmptyAttestationVerifier);
    let runtime = RuntimeImplementation::new(attestation_behavior);
    let mut client = schema::TrustedRuntimeClient::new(TrustedRuntime::serve(runtime));

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = schema::Initialization {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    client.initialize(&request).into_ok().unwrap();

    let request = schema::LookupData {
        items: vec![schema::LookupDataEntry {
            key: LOOKUP_TEST_KEY.to_vec(),
            value: LOOKUP_TEST_VALUE.to_vec(),
        }],
    };
    client.update_lookup_data(&request).into_ok().unwrap();

    let mut user_client = GenericAttestationClient::create(
        TestUserClient { inner: client },
        AttestationBehavior::create(EmptyAttestationGenerator, PlaceholderAmdAttestationVerifier),
    )
    .await
    .expect("failed to perform handshake");

    let lookup_response = {
        // Get the response from the runtime, and assert that no errors occured have occured on the
        // Oak IDL layer.
        let lookup_result = user_client.message(LOOKUP_TEST_KEY).await;
        assert_matches!(lookup_result, Ok(_));
        // Now parse the result with the Oak ABI response proto
        let decoded_response = oak_functions_abi::Response::decode(&lookup_result.unwrap());
        assert_matches!(
            decoded_response,
            Ok(oak_functions_abi::Response {
                status: oak_functions_abi::StatusCode::Success,
                ..
            })
        );
        decoded_response.unwrap()
    };

    assert_matches!(lookup_response.body(), Ok(body) if body == LOOKUP_TEST_VALUE);
}
