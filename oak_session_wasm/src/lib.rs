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
use js_sys::Math;
use oak_proto_rust::oak::session::v1::{
    PlaintextMessage, SessionRequest, SessionRequestWithSessionId, SessionResponse,
};
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ClientSession,
    ProtocolEngine, Session,
};
use prost::Message;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct WasmClientSession {
    inner: ClientSession,
    // Used by the server to identify the client session
    session_id: Vec<u8>,
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

        // Generate a random 16-byte session ID
        let session_id: Vec<u8> = (0..16).map(|_| (Math::random() * 256.0) as u8).collect();

        Ok(WasmClientSession { inner, session_id })
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
        self.inner
            .write(PlaintextMessage { plaintext: plaintext.to_vec() })
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Attempts to find a message containing ciphertext in the queue of
    /// incoming messages, that is held in the state-machine. If one is
    /// found decrypts the ciphertext and returns the plaintext.
    ///
    /// This function can be called multiple times in a row.
    #[wasm_bindgen]
    pub fn read(&mut self) -> Result<Option<Vec<u8>>, JsValue> {
        self.inner
            .read()
            .map(|opt_msg: Option<PlaintextMessage>| opt_msg.map(|msg| msg.plaintext))
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Puts a message received from the peer into the state-machine.
    ///
    /// The message is a byte-encoded protobuf message of the type
    /// `type.googleapis.com/oak.session.v1.SessionResponse`.
    #[wasm_bindgen]
    pub fn put_incoming_message(
        &mut self,
        incoming_message: &[u8],
    ) -> Result<PutIncomingMessageResult, JsValue> {
        let session_response: SessionResponse = SessionResponse::decode(incoming_message)
            .map_err(|e| JsValue::from_str(&e.to_string()))?;

        self.inner
            .put_incoming_message(session_response)
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
    /// `type.googleapis.com/oak.session.v1.
    /// SessionRequestWithSessionId`.
    #[wasm_bindgen]
    pub fn get_outgoing_message(&mut self) -> Result<Option<Vec<u8>>, JsValue> {
        self.inner
            .get_outgoing_message()
            .map(|opt_msg: Option<SessionRequest>| {
                opt_msg.map(|session_request| {
                    let session_request_with_id = SessionRequestWithSessionId {
                        session_id: self.session_id.clone(),
                        request: Some(session_request),
                    };
                    session_request_with_id.encode_to_vec()
                })
            })
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }
}
