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

    // The core types for working with sessions.
    pub use oak_session::{ClientSession, ServerSession};

    // We will also need to configure the sessions. The types in the next block help with that.
    pub use oak_session::{
        attestation::AttestationType,
        config::{SessionConfig, SessionConfigBuilder},
        handshake::HandshakeType,
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
use intro_import::*;

// In this simple example, we show the basics of passing messages back and forth
// bewteen an Oak ClientSession and an Oak ServerSession. In most real-world
// scenarios, you won't have the server and the client located right next to
// each other like this. For a slightly more realistic example, see
// unattested_pair_split.
fn main() {
    // Create a client session configured with non attestation, and using "NN" noise
    // handshake. For most of the examples here we will use the NoiseNN handshake
    // type, an unauthenticated key exchange.
    let client_config_builder: SessionConfigBuilder =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN);
    let mut client_session = ClientSession::create(client_config_builder.build())
        .expect("Failed to create client session");

    // Create a server session matching the client session described above.
    let server_config_builder: SessionConfigBuilder =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN);
    let mut server_session = ServerSession::create(server_config_builder.build())
        .expect("Failed to create server session");

    // To start the communications channel, we need to go through the initialization
    // sequence. This includes attestation exchanges, attestation verifications,
    // session bindings, and crypto handshakes.
    //
    // The following sequence works for initialization sequences in any session
    // configuration.
    //
    // Note that in most real use cases, the sender and receiver side will have a
    // loop like this. See unattested_pair_split for a more realistic example.
    while !client_session.is_open() && !server_session.is_open() {
        // The client will send the next init request.
        let init: SessionRequest = client_session
            .get_outgoing_message()
            .expect("Failure getting next message")
            .expect("Library Bug: Expected another init message but didn't get one.");

        // The server will receive the next init request
        // A failure could occur if the client sends the wrong kind of message,
        // for example, sending an encrypted message when the initialization
        // sequence is still in process.
        server_session.put_incoming_message(init).expect("Failed to put incoming message.");

        // The server *may* have a response.
        let init_response: Option<SessionResponse> =
            server_session.get_outgoing_message().expect("Failure getting next outgoing message");

        if let Some(init_response) = init_response {
            client_session
                .put_incoming_message(init_response)
                .expect("Failed to put client incoming message");
        }
    }

    println!("Open!");

    // Send one message client to server.
    let message = "Hello Server";
    println!("Client is writing: {message}");
    client_session
        .write(PlaintextMessage { plaintext: message.as_bytes().to_vec() })
        .expect("Unable to write message.");

    let out_to_server = client_session
        .get_outgoing_message()
        .expect("Failed getting next outgoing message")
        .expect(
            "Library bug: just wrote an message to encrypt but an encrypted output is not ready",
        );

    // Accept and decrypt the message at the server
    server_session.put_incoming_message(out_to_server).expect("Failed to put the server message");
    let server_read = server_session
        .read()
        .expect("Failure reading from session")
        .expect("Library Bug: Failed to read a message");
    let str_message = String::from_utf8_lossy(server_read.plaintext.as_slice());
    println!("The server read back: {str_message}");
}
