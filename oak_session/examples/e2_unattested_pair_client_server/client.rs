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

#[rustfmt::skip]
// Wrapping this section in an unformatted module to control how we explain the imports.
mod intro_import {
    // We'll need to import a few types to use oak_session. Some of the imports are
    // obvious, some less so.

    // Let's start simple: of course we need the session type itself.
    pub use oak_session::session::{ClientSession};

    // We will also need to configure the session. The types in the next block help with that.
    pub use oak_session::{
        config::{SessionConfig},
    };

    // The oak_session protocol uses protocol buffers as its main API.
    pub use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};

    // Now, for a few less obvious imports: The traits that drive the session interface.

    // This trait implements the "protocol" side of the session: sending/receiving messages on the
    // communications channel. It provides the `get_outgoing_message` and `put_incoming_message`
    // functions.
    pub use oak_session::ProtocolEngine;

    // This trait implements the "user" side of the session: writing messages to be encrypted, and
    // reading messages that have been decrypted. It provides the `read` and `write` methods.
    pub use oak_session::Session;
}

pub use intro_import::*;

// This is just a placeholder until we have a better library-provided client
// pattern.
pub struct Client {
    session: ClientSession,
}

impl Client {
    pub fn new(config: SessionConfig) -> Self {
        Self { session: ClientSession::create(config).expect("Failed to create client session") }
    }

    pub fn is_open(&self) -> bool {
        self.session.is_open()
    }

    pub fn get_init_request(&mut self) -> Option<SessionRequest> {
        if self.session.is_open() {
            return None;
        }
        self.session
            .get_outgoing_message()
            .expect("Failure getting next message")
            .expect("Library Bug: Expected another init message but didn't get one.")
            .into()
    }

    pub fn put_init_response(&mut self, init_response: SessionResponse) {
        self.session.put_incoming_message(init_response).expect("Failed to put incoming message");
    }

    pub fn encrypt_request(&mut self, message: &[u8]) -> SessionRequest {
        self.session
            .write(PlaintextMessage { plaintext: message.to_vec() })
            .expect("Failed to write message for encryption");
        self.session.get_outgoing_message().expect("Failed getting next outgoing message").expect(
            "Library bug: just wrote an message to encrypt but an encrypted output is not ready",
        )
    }

    pub fn decrypt_response(&mut self, response: SessionResponse) -> Vec<u8> {
        self.session.put_incoming_message(response).expect("Failed to put incoming message");
        self.session
            .read()
            .expect("Failed to read decrypted message")
            .expect("Decrypted message was empty")
            .plaintext
    }
}
