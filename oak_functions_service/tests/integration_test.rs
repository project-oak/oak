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
use oak_crypto::{
    schema::{AeadEncryptedMessage, HpkeRequest, HpkeResponse},
    SenderCryptoProvider,
};
use oak_functions_service::{
    schema::{self, OakFunctionsServer},
    OakFunctionsService,
};
use oak_remote_attestation_amd::PlaceholderAmdAttestationGenerator;
use prost::Message;
use std::sync::Arc;

const MOCK_CONSTANT_RESPONSE_SIZE: u32 = 1024;
const LOOKUP_TEST_KEY: &[u8] = b"test_key";
const LOOKUP_TEST_VALUE: &[u8] = b"test_value";
const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

#[test]
fn it_should_not_handle_user_requests_before_initialization() {
    let service = OakFunctionsService::new(Arc::new(PlaceholderAmdAttestationGenerator));
    let mut client = schema::OakFunctionsClient::new(OakFunctionsServer::new(service));

    let request = schema::InvokeRequest {
        body: vec![1, 2, 3],
    };
    let result = client.invoke(&request).into_ok();

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
    let service = OakFunctionsService::new(Arc::new(PlaceholderAmdAttestationGenerator));
    let mut client = schema::OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("echo").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = schema::InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    let initialize_response = client.initialize(&request).into_ok().unwrap();

    // TODO(#3767): Refactor `oak_crypto` API to encapsulate the proto messages.
    // Encrypt request.
    let encryption_public_key = initialize_response
        .public_key_info
        .expect("no public key info returned")
        .public_key;
    let crypto_provider = SenderCryptoProvider::new(&encryption_public_key);
    let (serialized_encapsulated_public_key, request_encryptor) = crypto_provider
        .create_encryptor()
        .expect("couldn't create encryptor");
    let (request_ciphertext, _) = request_encryptor
        .encrypt(&[1, 2, 3], EMPTY_ASSOCIATED_DATA)
        .expect("couldn't encrypt request");

    let request = HpkeRequest {
        encrypted_message: Some(AeadEncryptedMessage {
            ciphertext: request_ciphertext,
            associated_data: EMPTY_ASSOCIATED_DATA.to_vec(),
        }),
        serialized_encapsulated_public_key: Some(serialized_encapsulated_public_key),
    };
    let mut serialized_request = vec![];
    request
        .encode(&mut serialized_request)
        .expect("couldn't serialize request");

    // Send invoke request.
    let invoke_request = schema::InvokeRequest {
        body: serialized_request,
    };
    let result = client.invoke(&invoke_request).into_ok();

    assert!(result.is_ok());
}

#[test]
fn it_should_only_initialize_once() {
    let service = OakFunctionsService::new(Arc::new(PlaceholderAmdAttestationGenerator));
    let mut client = schema::OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("echo").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = schema::InitializeRequest {
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
async fn it_should_support_lookup_data() {
    let service = OakFunctionsService::new(Arc::new(PlaceholderAmdAttestationGenerator));
    let mut client = schema::OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup").unwrap();
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = schema::InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    let initialize_response = client.initialize(&request).into_ok().unwrap();

    let chunk = schema::LookupDataChunk {
        items: vec![schema::LookupDataEntry {
            key: LOOKUP_TEST_KEY.to_vec(),
            value: LOOKUP_TEST_VALUE.to_vec(),
        }],
    };

    let request = schema::ExtendNextLookupDataRequest { chunk: Some(chunk) };

    client.extend_next_lookup_data(&request).into_ok().unwrap();
    client
        .finish_next_lookup_data(&schema::FinishNextLookupDataRequest {})
        .into_ok()
        .unwrap();

    // TODO(#3767): Refactor `oak_crypto` API to encapsulate the proto messages.
    // Encrypt request.
    let encryption_public_key = initialize_response
        .public_key_info
        .expect("no public key info returned")
        .public_key;
    let crypto_provider = SenderCryptoProvider::new(&encryption_public_key);
    let (serialized_encapsulated_public_key, request_encryptor) = crypto_provider
        .create_encryptor()
        .expect("couldn't create encryptor");
    let (request_ciphertext, response_decryptor) = request_encryptor
        .encrypt(LOOKUP_TEST_KEY, EMPTY_ASSOCIATED_DATA)
        .expect("couldn't encrypt request");

    let request = HpkeRequest {
        encrypted_message: Some(AeadEncryptedMessage {
            ciphertext: request_ciphertext,
            associated_data: EMPTY_ASSOCIATED_DATA.to_vec(),
        }),
        serialized_encapsulated_public_key: Some(serialized_encapsulated_public_key),
    };
    let mut serialized_request = vec![];
    request
        .encode(&mut serialized_request)
        .expect("couldn't serialize request");

    let lookup_response = client
        .invoke(&schema::InvokeRequest {
            body: serialized_request,
        })
        .into_ok()
        .unwrap();

    // Decrypt response.
    let serialized_response = lookup_response.body;
    let response =
        HpkeResponse::decode(serialized_response.as_ref()).expect("couldn't deserialize response");
    let encrypted_message = response
        .encrypted_message
        .expect("response doesn't contain encrypted message");
    let (response_plaintext, _) = response_decryptor
        .decrypt(
            &encrypted_message.ciphertext,
            &encrypted_message.associated_data,
        )
        .expect("couldn't decrypt response");

    assert_eq!(LOOKUP_TEST_VALUE, response_plaintext);
}
