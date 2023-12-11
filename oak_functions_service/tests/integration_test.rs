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

use benchmark::proto::{benchmark_request::Action, BenchmarkRequest, EchoAndPanicTest};
use core::assert_matches::assert_matches;
use oak_crypto::{
    encryptor::{ClientEncryptor, EncryptionKeyProvider},
    proto::oak::crypto::v1::EncryptedRequest,
};
use oak_functions_service::{
    proto::oak::functions::{
        ExtendNextLookupDataRequest, FinishNextLookupDataRequest, InitializeRequest, InvokeRequest,
        LookupDataChunk, LookupDataEntry, OakFunctionsClient, OakFunctionsServer,
    },
    OakFunctionsService,
};
use oak_remote_attestation::proto::oak::attestation::v1::Evidence;
use prost::Message;
use std::sync::Arc;

const MOCK_CONSTANT_RESPONSE_SIZE: u32 = 1024;
const LOOKUP_TEST_KEY: &[u8] = b"test_key";
const LOOKUP_TEST_VALUE: &[u8] = b"test_value";
const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

fn init() {
    // See https://github.com/rust-cli/env_logger/#in-tests.
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Trace)
        .try_init();
}

fn new_service_for_testing() -> OakFunctionsService {
    OakFunctionsService::new(
        Evidence::default(),
        Arc::new(EncryptionKeyProvider::generate()),
        None,
    )
}

#[test]
fn it_should_not_handle_user_requests_before_initialization() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    #[allow(clippy::needless_update)]
    let request = InvokeRequest {
        encrypted_request: Some(EncryptedRequest::default()),
        ..Default::default()
    };
    let result = client.handle_user_request(&request).into_ok();

    assert_matches!(
        result,
        Err(micro_rpc::Status {
            code: micro_rpc::StatusCode::FailedPrecondition,
            ..
        })
    );
}

#[test]
fn it_should_handle_user_requests_after_initialization() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("echo").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    let initialize_response = client.initialize(&request).into_ok().unwrap();
    #[allow(deprecated)]
    let server_encryption_public_key = initialize_response
        .public_key_info
        .expect("no public key info returned")
        .public_key;

    // Encrypt request.
    let mut client_encryptor =
        ClientEncryptor::create(&server_encryption_public_key).expect("couldn't create encryptor");
    let encrypted_request = client_encryptor
        .encrypt(&[1, 2, 3], EMPTY_ASSOCIATED_DATA)
        .expect("couldn't encrypt request");

    // Send invoke request.
    #[allow(clippy::needless_update)]
    let invoke_request = InvokeRequest {
        encrypted_request: Some(encrypted_request),
        ..Default::default()
    };
    let result = client.handle_user_request(&invoke_request).into_ok();
    assert!(result.is_ok());
}

#[test]
fn it_should_only_initialize_once() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("echo").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };
    client.initialize(&request).into_ok().unwrap();

    let result = client.initialize(&request).into_ok();

    assert_matches!(
        result,
        Err(micro_rpc::Status {
            code: micro_rpc::StatusCode::FailedPrecondition,
            ..
        })
    );
}

#[tokio::test]
async fn it_should_error_on_invalid_wasm_module() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("invalid_module").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    let initialize_response = client.initialize(&request).into_ok().unwrap();
    #[allow(deprecated)]
    let server_encryption_public_key = initialize_response
        .public_key_info
        .expect("no public key info returned")
        .public_key;

    // TODO(#4274): Deduplicate this logic with Oak Client library.

    // Encrypt request.
    let mut client_encryptor =
        ClientEncryptor::create(&server_encryption_public_key).expect("couldn't create encryptor");
    let encrypted_request = client_encryptor
        .encrypt(LOOKUP_TEST_KEY, EMPTY_ASSOCIATED_DATA)
        .expect("couldn't encrypt request");

    // Send invoke request.
    let lookup_response = client
        .handle_user_request(
            #[allow(clippy::needless_update)]
            &InvokeRequest {
                encrypted_request: Some(encrypted_request),
                ..Default::default()
            },
        )
        .expect("couldn't receive response");
    assert!(lookup_response.is_ok());
    let encrypted_response = lookup_response
        .unwrap()
        .encrypted_response
        .expect("no encrypted response provided");

    // Decrypt response.
    let (response_bytes, _) = client_encryptor
        .decrypt(&encrypted_response)
        .expect("client couldn't decrypt response");

    let response = micro_rpc::ResponseWrapper::decode(response_bytes.as_slice())
        .map_err(|err| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                format!("couldn't deserialize response wrapper: {:?}", err),
            )
        })
        .expect("couldn't deserialize response wrapper");
    log::info!("response: {:?}", response);
    let response_result: Result<Vec<u8>, micro_rpc::Status> = response.into();
    log::info!("response_result: {:?}", response_result);

    // The error is encrypted and sent only to the client, and should say something about the Wasm
    // module not being valid. The error is mostly user facing, so its details may change in the
    // future, but here we check for a reasonable substring.
    assert!(response_result.is_err());
    let err = response_result.unwrap_err();
    assert_eq!(err.code, micro_rpc::StatusCode::Internal);
    assert_eq!(
        err.message,
        "couldn't validate `main` export: Func(ExportedFuncNotFound)"
    );
}

#[tokio::test]
async fn it_should_support_lookup_data() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    let initialize_response = client.initialize(&request).into_ok().unwrap();
    #[allow(deprecated)]
    let server_encryption_public_key = initialize_response
        .public_key_info
        .expect("no public key info returned")
        .public_key;

    let chunk = LookupDataChunk {
        items: vec![LookupDataEntry {
            key: LOOKUP_TEST_KEY.into(),
            value: LOOKUP_TEST_VALUE.into(),
        }],
    };

    let request = ExtendNextLookupDataRequest { chunk: Some(chunk) };

    client.extend_next_lookup_data(&request).into_ok().unwrap();
    client
        .finish_next_lookup_data(&FinishNextLookupDataRequest {})
        .into_ok()
        .unwrap();

    // TODO(#4274): Deduplicate this logic with Oak Client library.

    // Encrypt request.
    let mut client_encryptor =
        ClientEncryptor::create(&server_encryption_public_key).expect("couldn't create encryptor");
    let encrypted_request = client_encryptor
        .encrypt(LOOKUP_TEST_KEY, EMPTY_ASSOCIATED_DATA)
        .expect("couldn't encrypt request");

    // Send invoke request.
    let lookup_response = client
        .handle_user_request(
            #[allow(clippy::needless_update)]
            &InvokeRequest {
                encrypted_request: Some(encrypted_request),
                ..Default::default()
            },
        )
        .expect("couldn't receive response");
    assert!(lookup_response.is_ok());
    let encrypted_response = lookup_response
        .unwrap()
        .encrypted_response
        .expect("no encrypted response provided");

    // Decrypt response.
    let (response_bytes, _) = client_encryptor
        .decrypt(&encrypted_response)
        .expect("client couldn't decrypt response");

    let response = micro_rpc::ResponseWrapper::decode(response_bytes.as_slice())
        .map_err(|err| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                format!("couldn't deserialize response wrapper: {:?}", err),
            )
        })
        .expect("couldn't deserialize response wrapper");
    log::info!("response: {:?}", response);
    let response_result: Result<Vec<u8>, micro_rpc::Status> = response.into();
    log::info!("response_result: {:?}", response_result);

    assert_eq!(LOOKUP_TEST_VALUE, response_result.unwrap());
}

#[tokio::test]
async fn it_should_handle_wasm_panic() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    // Use the benchmark Wasm module, which contains a function that panics.
    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("benchmark").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    let initialize_response = client.initialize(&request).into_ok().unwrap();
    #[allow(deprecated)]
    let server_encryption_public_key = initialize_response
        .public_key_info
        .expect("no public key info returned")
        .public_key;

    // Encrypt request.
    let mut client_encryptor =
        ClientEncryptor::create(&server_encryption_public_key).expect("couldn't create encryptor");

    let request_data = vec![14, 12, 88];

    let request = BenchmarkRequest {
        action: Some(Action::EchoAndPanic(EchoAndPanicTest {
            data: request_data.clone(),
        })),
        iterations: 1,
    };

    let encrypted_request = client_encryptor
        .encrypt(&request.encode_to_vec(), EMPTY_ASSOCIATED_DATA)
        .expect("couldn't encrypt request");

    // Send invoke request.
    let lookup_response = client
        .handle_user_request(
            #[allow(clippy::needless_update)]
            &InvokeRequest {
                encrypted_request: Some(encrypted_request),
                ..Default::default()
            },
        )
        .expect("couldn't receive response");
    assert!(lookup_response.is_ok());
    let encrypted_response = lookup_response
        .unwrap()
        .encrypted_response
        .expect("no encrypted response provided");

    // Decrypt response.
    let (response_bytes, _) = client_encryptor
        .decrypt(&encrypted_response)
        .expect("client couldn't decrypt response");

    let response = micro_rpc::ResponseWrapper::decode(response_bytes.as_slice())
        .map_err(|err| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                format!("couldn't deserialize response wrapper: {:?}", err),
            )
        })
        .expect("couldn't deserialize response wrapper");
    log::info!("response: {:?}", response);
    let response_result: Result<Vec<u8>, micro_rpc::Status> = response.into();
    log::info!("response_result: {:?}", response_result);

    // The current behaviour is that the panic is ignored and the response is the latest value
    // written.
    assert_eq!(request_data, response_result.unwrap());
}
