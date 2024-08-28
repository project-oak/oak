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

use oak_proto_rust::oak::session::v1::SessionResponse;
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ClientSession,
    ProtocolEngine, Session,
};
use prost::Message;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct WasmClientSession {
    inner: ClientSession,
}

#[wasm_bindgen]
pub enum PutIncomingMessageResult {
    NoIncomingMessageExpected,
    Success,
}

#[wasm_bindgen]
impl WasmClientSession {
    #[wasm_bindgen(constructor)]
    pub fn create_unattested_noise_nn_session() -> Result<WasmClientSession, JsValue> {
        let config =
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
        let inner = ClientSession::create(config).map_err(|e| JsValue::from_str(&e.to_string()))?;
        Ok(WasmClientSession { inner })
    }

    /// Checks whether session is ready to send and receive encrypted messages.
    /// Session becomes ready once remote attestation and crypto handshake have
    /// been successfully finished.
    #[wasm_bindgen]
    pub fn is_open(&self) -> bool {
        self.inner.is_open()
    }

    /// Encrypts `plaintext` and adds it to the queue of outgoing messages in
    /// the state-machine.
    ///
    /// This function can be called multiple times in a row, which will result
    /// in multiple outgoing protocol messages being created.
    #[wasm_bindgen]
    pub fn write(&mut self, plaintext: &[u8]) -> Result<(), JsValue> {
        self.inner.write(plaintext).map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Attempts to find a message containing ciphertext in the queue of
    /// incoming messages, that is held in the state-machine. If one is
    /// found decrypts the ciphertext and returns the plaintext.
    ///
    /// This function can be called multiple times in a row.
    #[wasm_bindgen]
    pub fn read(&mut self) -> Result<Option<Vec<u8>>, JsValue> {
        self.inner.read().map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Puts a message received from the peer into the state-machine.
    ///
    /// The message is a byte-encoded protobuf message of the type
    /// `type.googleapis.com/oak.session.v1`. It may contain ciphertext,
    /// attestation evidence, or a handshake step.
    #[wasm_bindgen]
    pub fn put_incoming_message(
        &mut self,
        incoming_message: &[u8],
    ) -> Result<PutIncomingMessageResult, JsValue> {
        self.inner
            .put_incoming_message(
                &SessionResponse::decode(incoming_message)
                    .map_err(|e| JsValue::from_str(&e.to_string()))?,
            )
            .map(|opt_result| {
                opt_result
                    .map(|_| PutIncomingMessageResult::Success)
                    .unwrap_or(PutIncomingMessageResult::NoIncomingMessageExpected)
            })
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Gets the next message that needs to be sent to the peer
    /// from the state-machine.
    ///
    /// The message is a byte-encoded protobuf message of the type
    /// `type.googleapis.com/oak.session.v1`. It may contain ciphertext,
    /// attestation evidence, or a handshake step.
    #[wasm_bindgen]
    pub fn get_outgoing_message(&mut self) -> Result<Option<Vec<u8>>, JsValue> {
        self.inner
            .get_outgoing_message()
            .map(|opt_msg| opt_msg.map(|msg| msg.encode_to_vec()))
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }
}
