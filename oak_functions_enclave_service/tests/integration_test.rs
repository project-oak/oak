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
#![feature(never_type)]
#![feature(unwrap_infallible)]

extern crate alloc;

use alloc::sync::Arc;
use core::assert_matches::assert_matches;

use oak_client::verifier::extract_encryption_public_key;
use oak_crypto::encryptor::ClientEncryptor;
use oak_functions_enclave_service::OakFunctionsService;
use oak_micro_rpc::oak::functions::{
    OakFunctionsClient, OakFunctionsServer, testing::TestModuleClient,
};
use oak_proto_rust::oak::{
    crypto::v1::EncryptedRequest,
    functions::{
        ExtendNextLookupDataRequest, FinishNextLookupDataRequest, InitializeRequest, InvokeRequest,
        LookupDataChunk, LookupDataEntry, extend_next_lookup_data_request::Data,
        testing::EchoAndPanicRequest,
    },
};
use prost::Message;

const MOCK_CONSTANT_RESPONSE_SIZE: u32 = 1024;
const LOOKUP_TEST_KEY: &[u8] = b"test_key";
const LOOKUP_TEST_VALUE: &[u8] = b"test_value";
const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

fn init() {
    // See https://github.com/rust-cli/env_logger/#in-tests.
    let _ = env_logger::builder().is_test(true).filter_level(log::LevelFilter::Trace).try_init();
}

fn new_service_for_testing() -> OakFunctionsService<
    oak_restricted_kernel_sdk::testing::MockEncryptionKeyHandle,
    oak_restricted_kernel_sdk::testing::MockAttester,
    oak_functions_service::wasm::WasmHandler,
> {
    OakFunctionsService::new(
        oak_restricted_kernel_sdk::testing::MockAttester::create()
            .expect("failed to create EvidenceProvidder"),
        Arc::new(
            oak_restricted_kernel_sdk::testing::MockEncryptionKeyHandle::create()
                .expect("failed to create EncryptionKeyHandle"),
        ),
        None,
        Default::default(),
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
        Err(micro_rpc::Status { code: micro_rpc::StatusCode::FailedPrecondition, .. })
    );
}

#[test]
fn it_should_handle_user_requests_after_initialization() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = "oak_functions/examples/echo/echo.wasm";
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    let initialize_response = client.initialize(&request).into_ok().unwrap();
    let evidence =
        initialize_response.evidence.expect("initialize response doesn't have public key info");
    let server_encryption_public_key =
        extract_encryption_public_key(&evidence).expect("couldn't extract encryption public key");

    // Encrypt request.
    let mut client_encryptor =
        ClientEncryptor::create(&server_encryption_public_key).expect("couldn't create encryptor");
    let encrypted_request = client_encryptor
        .encrypt(&[1, 2, 3], EMPTY_ASSOCIATED_DATA)
        .expect("couldn't encrypt request");

    // Send invoke request.
    #[allow(clippy::needless_update)]
    let invoke_request =
        InvokeRequest { encrypted_request: Some(encrypted_request), ..Default::default() };
    let result = client.handle_user_request(&invoke_request).into_ok();
    assert!(result.is_ok());
}

#[test]
fn it_should_only_initialize_once() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = "oak_functions/examples/echo/echo.wasm";
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };
    client.initialize(&request).into_ok().unwrap();

    let result = client.initialize(&request).into_ok();

    assert_matches!(
        result,
        Err(micro_rpc::Status { code: micro_rpc::StatusCode::FailedPrecondition, .. })
    );
}

#[test]
fn it_should_error_on_invalid_wasm_module() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = "oak_functions/examples/invalid_module/invalid_module.wasm";
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    let initialize_response = client.initialize(&request).into_ok().unwrap();
    let evidence =
        initialize_response.evidence.expect("initialize response doesn't have public key info");
    let server_encryption_public_key =
        extract_encryption_public_key(&evidence).expect("couldn't extract encryption public key");

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
            &InvokeRequest { encrypted_request: Some(encrypted_request), ..Default::default() },
        )
        .expect("couldn't receive response");
    assert!(lookup_response.is_ok());
    let encrypted_response =
        lookup_response.unwrap().encrypted_response.expect("no encrypted response provided");

    // Decrypt response.
    let (response_bytes, _) =
        client_encryptor.decrypt(&encrypted_response).expect("client couldn't decrypt response");

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

    // The error is encrypted and sent only to the client, and should say something
    // about the Wasm module not being valid. The error is mostly user facing,
    // so its details may change in the future, but here we check for a
    // reasonable substring.
    assert!(response_result.is_err());
    let err = response_result.unwrap_err();
    assert_eq!(err.code, micro_rpc::StatusCode::Internal);
    assert_eq!(err.message, "couldn't validate `main` export: Func(ExportedFuncNotFound)");
}

#[test]
fn it_should_support_lookup_data() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    let wasm_path = "oak_functions/examples/key_value_lookup/key_value_lookup.wasm";
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    let initialize_response = client.initialize(&request).into_ok().unwrap();
    let evidence =
        initialize_response.evidence.expect("initialize response doesn't have public key info");
    let server_encryption_public_key =
        extract_encryption_public_key(&evidence).expect("couldn't extract encryption public key");

    let chunk = LookupDataChunk {
        items: vec![LookupDataEntry {
            key: LOOKUP_TEST_KEY.into(),
            value: LOOKUP_TEST_VALUE.into(),
        }],
    };

    let request = ExtendNextLookupDataRequest { data: Some(Data::Chunk(chunk)) };

    client.extend_next_lookup_data(&request).into_ok().unwrap();
    client.finish_next_lookup_data(&FinishNextLookupDataRequest {}).into_ok().unwrap();

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
            &InvokeRequest { encrypted_request: Some(encrypted_request), ..Default::default() },
        )
        .expect("couldn't receive response");
    assert!(lookup_response.is_ok());
    let encrypted_response =
        lookup_response.unwrap().encrypted_response.expect("no encrypted response provided");

    // Decrypt response.
    let (response_bytes, _) =
        client_encryptor.decrypt(&encrypted_response).expect("client couldn't decrypt response");

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

#[test]
fn it_should_handle_wasm_panic() {
    init();
    let service = new_service_for_testing();
    let mut client = OakFunctionsClient::new(OakFunctionsServer::new(service));

    // Use the Oak Functions test Wasm module, which contains a function that
    // panics.
    let wasm_path = "oak_functions_test_module/oak_functions_test_module.wasm";
    let wasm_bytes = std::fs::read(wasm_path).unwrap();
    let request = InitializeRequest {
        wasm_module: wasm_bytes,
        constant_response_size: MOCK_CONSTANT_RESPONSE_SIZE,
    };

    let initialize_response = client.initialize(&request).into_ok().unwrap();
    let evidence =
        initialize_response.evidence.expect("initialize response doesn't have public key info");
    let server_encryption_public_key =
        extract_encryption_public_key(&evidence).expect("couldn't extract encryption public key");

    struct Transport<'a> {
        oak_functions_client: &'a mut OakFunctionsClient<
            OakFunctionsServer<
                OakFunctionsService<
                    oak_restricted_kernel_sdk::testing::MockEncryptionKeyHandle,
                    oak_restricted_kernel_sdk::testing::MockAttester,
                    oak_functions_service::wasm::WasmHandler,
                >,
            >,
        >,
        server_encryption_public_key: &'a [u8],
    }

    impl micro_rpc::Transport for Transport<'_> {
        fn invoke(&mut self, request_bytes: &[u8]) -> Result<Vec<u8>, !> {
            log::debug!("request bytes: {:?}", request_bytes);

            let mut client_encryptor = ClientEncryptor::create(self.server_encryption_public_key)
                .expect("couldn't create encryptor");

            // Encrypt request.
            let encrypted_request = client_encryptor
                .encrypt(request_bytes, EMPTY_ASSOCIATED_DATA)
                .expect("couldn't encrypt request");

            // Send invoke request.
            let invoke_response = self
                .oak_functions_client
                .handle_user_request(
                    #[allow(clippy::needless_update)]
                    &InvokeRequest {
                        encrypted_request: Some(encrypted_request),
                        ..Default::default()
                    },
                )
                .expect("couldn't receive response");
            assert!(invoke_response.is_ok());

            let encrypted_response = invoke_response
                .unwrap()
                .encrypted_response
                .expect("no encrypted response provided");
            log::debug!("encrypted_response: {:?}", encrypted_response);

            // Decrypt response.
            let (response_outer_bytes, _associated_data) = client_encryptor
                .decrypt(&encrypted_response)
                .expect("client couldn't decrypt response");

            log::debug!("response outer bytes: {:?}", response_outer_bytes);

            // There is an additional layer of wrapping around the response, so we need to
            // unwrap it.
            let response_inner =
                micro_rpc::ResponseWrapper::decode(response_outer_bytes.as_slice())
                    .map_err(|err| {
                        micro_rpc::Status::new_with_message(
                            micro_rpc::StatusCode::Internal,
                            format!("couldn't deserialize response wrapper: {:?}", err),
                        )
                    })
                    .expect("couldn't deserialize inner response wrapper");
            let response_result: Result<Vec<u8>, micro_rpc::Status> = response_inner.into();

            log::debug!("response inner result: {:?}", response_result);

            Ok(response_result.unwrap())
        }
    }

    let transport = Transport {
        oak_functions_client: &mut client,
        server_encryption_public_key: &server_encryption_public_key,
    };

    let mut client = TestModuleClient::new(transport);

    let request_data = vec![1, 2, 3, 4, 5, 6, 7];

    let echo_and_panic_request = EchoAndPanicRequest { data: request_data.clone() };
    let echo_and_panic_response = client
        .echo_and_panic(&echo_and_panic_request)
        .into_ok()
        .expect("couldn't receive response");

    // The current behaviour is that the panic is ignored and the response is the
    // latest value written.
    assert_eq!(request_data, echo_and_panic_response.data);
}
