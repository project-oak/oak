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
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_session::{
    ClientSession, ProtocolEngine, Session, attestation::AttestationType, config::SessionConfig,
    handshake::HandshakeType,
};
use prost::Message;
use wasm_bindgen::prelude::*;

/// This is copied from oak_session/src/attestation.rs.
#[wasm_bindgen]
pub enum OakAttestationType {
    Bidirectional,
    SelfUnidirectional,
    PeerUnidirectional,
    Unattested,
}

impl From<OakAttestationType> for AttestationType {
    fn from(attestation_type: OakAttestationType) -> Self {
        match attestation_type {
            OakAttestationType::Bidirectional => AttestationType::Bidirectional,
            OakAttestationType::SelfUnidirectional => AttestationType::SelfUnidirectional,
            OakAttestationType::PeerUnidirectional => AttestationType::PeerUnidirectional,
            OakAttestationType::Unattested => AttestationType::Unattested,
        }
    }
}

/// This is copied from oak_session/src/handshake.rs.
#[wasm_bindgen]
pub enum OakHandshakeType {
    NoiseKK,
    NoiseKN,
    NoiseNK,
    NoiseNN,
}

impl From<OakHandshakeType> for HandshakeType {
    fn from(handshake_type: OakHandshakeType) -> Self {
        match handshake_type {
            OakHandshakeType::NoiseKK => HandshakeType::NoiseKK,
            OakHandshakeType::NoiseKN => HandshakeType::NoiseKN,
            OakHandshakeType::NoiseNK => HandshakeType::NoiseNK,
            OakHandshakeType::NoiseNN => HandshakeType::NoiseNN,
        }
    }
}
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
    pub fn create_oak_session(
        attestation_type: OakAttestationType,
        handshake_type: OakHandshakeType,
    ) -> Result<WasmClientSession, JsValue> {
        let config = SessionConfig::builder(
            AttestationType::from(attestation_type),
            HandshakeType::from(handshake_type),
        )
        .build();
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
                opt_msg.map(|session_request| session_request.encode_to_vec())
            })
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    #[wasm_bindgen]
    pub fn get_outgoing_message_json(&mut self) -> Result<Option<Vec<u8>>, JsValue> {
        self.inner
            .get_outgoing_message()
            .map(|opt_msg: Option<SessionRequest>| {
                opt_msg.map(|session_request| serde_json::to_vec(&session_request).unwrap())
            })
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Puts a message received from the peer into the state-machine.
    ///
    /// The message is a byte-encoded protobuf message of the type
    /// `type.googleapis.com/oak.session.v1.SessionResponse`.
    #[wasm_bindgen]
    pub fn put_incoming_message_json(
        &mut self,
        incoming_message: &[u8],
    ) -> Result<PutIncomingMessageResult, JsValue> {
        let session_response: SessionResponse = serde_json::from_slice(incoming_message)
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

    /// Derives the key-exchange key (KEK) from the user secret.
    ///
    /// The `user_secret` is an arbitrary byte array, and the `kek_version` is
    /// the version of the KEK. The `salt` is a 16-byte array.
    ///
    /// The function returns a 256-bit key, or an error if the input is
    /// invalid.
    #[wasm_bindgen]
    pub fn derive_kek(
        user_secret: &[u8],
        kek_version: i32,
        salt: &[u8],
    ) -> Result<Vec<u8>, JsValue> {
        Ok(user_info_derive::derive_kek(user_secret, kek_version, salt))
    }

    #[wasm_bindgen]
    pub fn derive_pm_uid(user_secret: &[u8]) -> Result<String, JsValue> {
        Ok(user_info_derive::derive_pm_uid(user_secret))
    }
}
