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
    // Now that most of the session-related logic is moved into client/server
    // components, the main includes are simpler to follow.

    // Our sessions are now warpped in this components
    pub use server::ServerComponent;
    pub use client::Client;

    // We will also need to configure the sessions. The types in the next block help with that.
    pub use oak_session::{
        attestation::AttestationType,
        config::{SessionConfig},
        handshake::HandshakeType,
    };
}

use intro_import::*;
fn main() {
    let client_config: SessionConfig =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let mut client = Client::new(client_config);

    let server_config: SessionConfig =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let (server_component, request_tx, response_rx) = ServerComponent::new(server_config);
    std::thread::spawn(move || {
        server_component.run();
    });

    // To start the communications channel, we need to go through the initialization
    // sequence. This includes attestation exchanges, attestation verifications,
    // session bindings, and crypto handshaakes.
    //
    // The following sequence works for initialization sequences in any session
    // configuration.
    //
    // The idea is that while the client is not open, it will have the next
    // initialization message ready. So we send that the server.
    //
    // After that, the client may be expected a server response. So if it's still
    // not open, we expect to the next incoming message from the server to be an
    // init message, and act accordingly.
    while !client.is_open() {
        request_tx
            .send(client.get_init_request().expect("Expected client to have init message ready."))
            .expect("failed to send init request");

        if !client.is_open() {
            client.put_init_response(response_rx.recv().expect("Failed to receive init response"));
        }
    }

    // Send one message client to server.
    let message = "Hello Server";
    println!("Client is writing: {message}");

    // Encrypt and send the message.
    let out_to_server = client.encrypt_request(message.as_bytes());
    request_tx.send(out_to_server).expect("Failed to send response");

    // Receive and decrypt the response.
    let response = response_rx.recv().expect("Failed to read response");
    let decrypted = client.decrypt_response(response);

    // Print it out and shut the server down.
    let str_message = String::from_utf8_lossy(decrypted.as_slice());
    println!("Server responded: {str_message}");
    drop(request_tx);
}
