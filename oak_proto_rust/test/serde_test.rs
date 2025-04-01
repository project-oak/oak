//
// Copyright 2025 The Project Oak Authors
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

use oak_proto_rust::oak::session::v1::NoiseHandshakeMessage;
use prost::Message;

#[test]
fn proto_to_json_succeeds() {
    let msg = NoiseHandshakeMessage {
        ephemeral_public_key: "aabb".as_bytes().to_vec(),
        ..Default::default()
    };
    let json_str = serde_json::to_string(&msg);

    assert!(json_str.is_ok());
    let json_str = json_str.unwrap();

    let expected_str =
        "{\"ephemeralPublicKey\":\"YWFiYg==\",\"staticPublicKey\":\"\",\"ciphertext\":\"\"}";
    assert_eq!(json_str, expected_str);
}

#[test]
fn json_to_proto_succeeds() {
    let json_str =
        "{\"ephemeralPublicKey\":\"YWFiYg==\",\"staticPublicKey\":\"\",\"ciphertext\":\"\"}";
    let msg = serde_json::from_str::<NoiseHandshakeMessage>(json_str);
    assert!(msg.is_ok());
    let msg = msg.unwrap();
    let expected_msg = NoiseHandshakeMessage {
        ephemeral_public_key: "aabb".as_bytes().to_vec(),
        ..Default::default()
    };

    assert_eq!(msg.encode_to_vec(), expected_msg.encode_to_vec());
}
