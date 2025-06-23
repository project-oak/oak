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
    pub use oak_session::session::{ServerSession};

    // We will also need to configure the sessions. The types in the next block help with that.
    // Since the caller creates the `SessionConfig`, we only need to worry about that type,
    // and not the various types used to create it in the first example.
    pub use oak_session::{ config::SessionConfig };

    // The oak_session protocol uses protocol buffers as its main API.
    pub use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};

    // Now, for a few less obvious imports: The traits that drive the session interface.

    // This trait implements the "protocol" side of the session: sending/receiving messages on the
    // communications channel. It provides the `get_outgoing_message` and `put_incoming_message`
    // functions.
    pub use oak_session::ProtocolEngine;

    // This trait implements the "user" side of the session: writing messages to be encrypted, and
    // reading messages that have been decrypted. It provides the `read` and `write` methods.
    pub use oak_session::Session;
}

use std::sync::mpsc;

pub use intro_import::*;

// The server component is a generic representation of some sort of server
// handler for a communications channel. To keep things simple, we'll just use a
// simple Rust channel to implement the I/O. In reality, this would be smoething
// like a gRPC client.
pub struct ServerComponent {
    session: ServerSession,
    resp_tx: mpsc::Sender<SessionResponse>,
    req_rx: mpsc::Receiver<SessionRequest>,
}

impl ServerComponent {
    pub fn new(
        config: SessionConfig,
    ) -> (Self, mpsc::Sender<SessionRequest>, mpsc::Receiver<SessionResponse>) {
        let (resp_tx, resp_rx) = mpsc::channel();
        let (req_tx, req_rx) = mpsc::channel();
        (
            Self {
                resp_tx,
                req_rx,
                session: ServerSession::create(config).expect("Failed to create client session"),
            },
            req_tx,
            resp_rx,
        )
    }
    pub fn run(mut self) {
        println!("Server starting");
        for req in self.req_rx.iter() {
            let was_open = self.session.is_open();
            self.session.put_incoming_message(req).expect("Failed to put incoming message.");
            if !was_open {
                // If the session isn't open, we must still be in the initialization phase.
                // So we consume the request, and then send a response if there is one.
                let maybe_response = self
                    .session
                    .get_outgoing_message()
                    .expect("Failed to check for next outgoing message");
                if let Some(resp) = maybe_response {
                    self.resp_tx.send(resp).expect("failed to send response on channel");
                }
            } else {
                // The session is open. So just consume the message and response.
                let mut request =
                    self.session.read().expect("Failed to read decrypted message").expect(
                        "Library error: expected decrypted message but nothing was provided",
                    );
                request.plaintext.reverse();
                self.session.write(request).expect("failed to write request for encryption");
                let enc_response = self
                    .session
                    .get_outgoing_message()
                    .expect("Failed to get encrypted outgoing message")
                    .expect("Library error");
                self.resp_tx.send(enc_response).expect("Failed to send response on channel");
            }
        }
        println!("Server completed.")
    }
}
