//
// Copyright 2024 The Project Oak Authors
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

mod proto {
    pub mod oak {
        pub mod test {
            tonic::include_proto!("oak.test");
        }
    }
}

// Test to confirm that the dependency on micro_rpc and its own protobuf types
// works correctly.
#[test]
fn micro_rpc_dep_test() {
    let response_wrapper: micro_rpc::ResponseWrapper =
        Err(micro_rpc::Status::new_with_message(micro_rpc::StatusCode::InvalidArgument, "error"))
            .into();
    assert_eq!(
        format!("{response_wrapper:?}"),
        r##"ResponseWrapper { response: Some(Error(Status { code: 3, message: "error" })) }"##
    );
}

// Test to confirm that the dependency on oak_crypto and its own protobuf types
// works correctly.
#[test]
fn oak_crypto_dep_test() {
    let request_wrapper = proto::oak::test::TestRequestWrapper {
        encrypted_request: Some(oak_proto_rust::oak::crypto::v1::EncryptedRequest {
            encrypted_message: Some(oak_proto_rust::oak::crypto::v1::AeadEncryptedMessage {
                associated_data: vec![],
                nonce: vec![],
                ciphertext: vec![],
            }),
            serialized_encapsulated_public_key: Some(vec![]),
        }),
    };

    assert_eq!(
        format!("{request_wrapper:?}"),
        r##"TestRequestWrapper { encrypted_request: Some(EncryptedRequest { encrypted_message: Some(AeadEncryptedMessage { ciphertext: [], associated_data: [], nonce: [] }), serialized_encapsulated_public_key: Some([]) }) }"##
    );
}
