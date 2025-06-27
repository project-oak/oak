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
    // The core types for working with sessions.
    pub use oak_session::{ClientSession, ServerSession};

    // We will also need to configure the sessions. The types in the next block help with that.
    pub use oak_session::{
        attestation::AttestationType,
        config::{SessionConfig, SessionConfigBuilder},
        handshake::HandshakeType,
    };

    // This trait provides the `is_open` method that we use during handshake.
    pub use oak_session::Session;

    // These traits provide an easier-to-use interface over the ClientSession and ServerSession.
    pub use oak_session::channel::{SessionInitializer, SessionChannel};
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
        if !client_session.is_open() {
            // The client will send the next init request.
            let request = client_session.next_init_message().expect("Failed to get init message");
            // The server will receive the next init request
            // A failure could occur if the client sends the wrong kind of message,
            // for example, sending an encrypted message when the initialization
            // sequence is still in process.
            server_session
                .handle_init_message(request)
                .expect("server failed to handle init request");
        }

        // The server *may* have a response.
        if !server_session.is_open() {
            let init_response =
                server_session.next_init_message().expect("failed to get server init response");

            client_session
                .handle_init_message(init_response)
                .expect("Failed to handle server init response");
        }
    }

    println!("Open!");

    // Send one message client to server.
    let message = "Hello Server";
    println!("Client is writing: {message}");
    let to_server = client_session.encrypt(message).expect("failed to encrypt message");

    // Accept and decrypt the message at the server
    let server_read =
        server_session.decrypt(to_server).expect("failed to decrypt message at server");
    let str_message = String::from_utf8_lossy(server_read.as_slice());
    println!("The server read back: {str_message}");
}
