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

use std::collections::VecDeque;

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

/// FakeWasmClientSession is a simplified client session implementation used for
/// testing purposes. It does not perform any encryption or decryption, and does
/// not wrap ciphertext in proto messages. Instead it treats all messages as
/// plaintext. This mock is particularly useful for tests the frontend logic in
/// cases for tests and prototypes, where encryption is is not implemented by
/// the backend.
#[wasm_bindgen]
pub struct FakeWasmClientSession {
    /// Queue of outgoing messages (plaintext)
    outgoing_messages: VecDeque<Vec<u8>>,
    /// Queue of incoming messages (plaintext)
    incoming_messages: VecDeque<Vec<u8>>,
}

#[wasm_bindgen]
impl FakeWasmClientSession {
    /// Creates a new FakeWasmClientSession.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        FakeWasmClientSession {
            outgoing_messages: VecDeque::new(),
            incoming_messages: VecDeque::new(),
        }
    }

    /// Always returns true, as this mock session is considered always open
    /// since there's no handshake being performed.
    #[wasm_bindgen]
    pub fn is_open(&self) -> bool {
        true
    }

    /// Queues the plaintext message for sending without any encryption.
    /// This method simulates the writing of a message in a real session.
    #[wasm_bindgen]
    pub fn write(&mut self, plaintext: &[u8]) -> Result<(), JsValue> {
        self.outgoing_messages.push_back(plaintext.to_vec());
        Ok(())
    }

    /// Retrieves the next available incoming message as plaintext.
    /// This method simulates reading and decrypting a message in a real
    /// session.
    #[wasm_bindgen]
    pub fn read(&mut self) -> Result<Option<Vec<u8>>, JsValue> {
        Ok(self.incoming_messages.pop_front())
    }

    /// Queues an incoming message as plaintext without any decryption.
    /// This method simulates receiving an encrypted message in a real session.
    ///
    /// Unlike in a real session, the incoming message is neither encrypted nor
    /// wrapped in protos.
    #[wasm_bindgen]
    pub fn put_incoming_message(
        &mut self,
        incoming_message: &[u8],
    ) -> Result<PutIncomingMessageResult, JsValue> {
        self.incoming_messages.push_back(incoming_message.to_vec());
        Ok(PutIncomingMessageResult::Success)
    }

    /// Retrieves the next outgoing message as plaintext.
    /// This method simulates getting an encrypted message ready for sending in
    /// a real session.
    ///
    /// Unlike in a real session, the outgoing message is neither encrypted nor
    /// wrapped in protos.
    #[wasm_bindgen]
    pub fn get_outgoing_message(&mut self) -> Result<Option<Vec<u8>>, JsValue> {
        Ok(self.outgoing_messages.pop_front())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_put_incoming_message_and_read() {
        let mut session = FakeWasmClientSession::new();
        let message1 = b"Hello, World!";
        let message2 = b"Another message";

        // Put incoming messages
        session.put_incoming_message(message1).unwrap();
        session.put_incoming_message(message2).unwrap();

        // Read the messages
        let read_message1 = session.read().unwrap().unwrap();
        let read_message2 = session.read().unwrap().unwrap();

        assert_eq!(read_message1, message1);
        assert_eq!(read_message2, message2);

        // Ensure the queue is now empty
        assert!(session.read().unwrap().is_none());
    }

    #[test]
    fn test_write_and_get_outgoing_message() {
        let mut session = FakeWasmClientSession::new();
        let message1 = b"Outgoing message 1";
        let message2 = b"Outgoing message 2";

        // Write the messages
        session.write(message1).unwrap();
        session.write(message2).unwrap();

        // Get outgoing messages
        let outgoing_message1 = session.get_outgoing_message().unwrap().unwrap();
        let outgoing_message2 = session.get_outgoing_message().unwrap().unwrap();

        assert_eq!(outgoing_message1, message1);
        assert_eq!(outgoing_message2, message2);

        // Ensure the queue is now empty
        assert!(session.get_outgoing_message().unwrap().is_none());
    }

    #[test]
    fn test_multiple_operations() {
        let mut session = FakeWasmClientSession::new();
        let incoming1 = b"Incoming 1";
        let incoming2 = b"Incoming 2";
        let outgoing1 = b"Outgoing 1";
        let outgoing2 = b"Outgoing 2";

        // Put incoming messages and write outgoing messages
        session.put_incoming_message(incoming1).unwrap();
        session.write(outgoing1).unwrap();
        session.put_incoming_message(incoming2).unwrap();
        session.write(outgoing2).unwrap();

        // Verify incoming messages
        assert_eq!(session.read().unwrap().unwrap(), incoming1);
        assert_eq!(session.read().unwrap().unwrap(), incoming2);
        assert!(session.read().unwrap().is_none());

        // Verify outgoing messages
        assert_eq!(session.get_outgoing_message().unwrap().unwrap(), outgoing1);
        assert_eq!(session.get_outgoing_message().unwrap().unwrap(), outgoing2);
        assert!(session.get_outgoing_message().unwrap().is_none());
    }
}
