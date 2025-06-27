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
    // The ServerSession is the core struct for working with a session on the server side.
    pub use oak_session::session::{ServerSession};

    // We will also need to configure the sessions. The types in the next block help with that.
    // Since the caller creates the `SessionConfig`, we only need to worry about that type,
    // and not the various types used to create it in the first example.
    pub use oak_session::{config::SessionConfig };

    // The oak_session protocol uses protocol buffers as its main API.
    pub use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};

    // This trait provides the `is_open` method that we need during initialization.
    pub use oak_session::Session;

    // These traits provide an easier-to-use interface over the ClientSession and ServerSession.
    pub use oak_session::channel::{SessionInitializer, SessionChannel};
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
            if self.session.is_open() {
                // If the server is open, we can decrypt the message, process it, and respond.
                let mut request = self.session.decrypt(req).expect("failed to decrypt request");

                request.reverse();

                let response = self.session.encrypt(request).expect("failed to encrypt response");
                self.resp_tx.send(response).expect("Failed to send response on channel");
            } else {
                // If the session isn't open yet, we should assume the incoming message is an
                // init message.
                self.session.handle_init_message(req).expect("failed to handle init request");

                // If the session still isn't open, we must have an init response to return.
                if !self.session.is_open() {
                    let next =
                        self.session.next_init_message().expect("failed to get init response");
                    self.resp_tx.send(next).expect("failed to send next init response")
                }
            }
        }
        println!("Server completed.")
    }
}
