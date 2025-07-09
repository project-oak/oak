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

// Wrapping this section in an unformatted module to control how we explain the
// imports.
#[rustfmt::skip]
mod intro_import {
    // The server is now wrapped in this components
    pub use server::ServerComponent;

    // We'll work directly with the client session here.
    pub use oak_session::session::ClientSession;

    // These traits provide an easier-to-use interface over the ClientSession and ServerSession.
    pub use oak_session::channel::{SessionInitializer, SessionChannel};

    // This trait provides the `is_open` method that we use during handshake.
    pub use oak_session::session::Session;

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
    let mut client = ClientSession::create(client_config).expect("failed to create client");

    let server_config: SessionConfig =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let (server_component, request_tx, response_rx) = ServerComponent::new(server_config);
    let server_handle = std::thread::spawn(move || {
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

    // Handshake sequence
    while !client.is_open() {
        let request = client.next_init_message().expect("failed to get client init message");
        request_tx.send(request).expect("failed to send init requets");
        if !client.is_open() {
            let response = response_rx.recv().expect("failed to get next server message");
            client.handle_init_message(response).expect("failed to handle init response");
        }
    }

    // Send one message client to server.
    let message = "Hello Server";
    println!("Client is writing: {message}");

    // Encrypt and send the message.
    let out_to_server = client.encrypt(message.as_bytes()).expect("failed to encrypt message");
    request_tx.send(out_to_server).expect("Failed to send response");

    // Receive and decrypt the response.
    let response = response_rx.recv().expect("Failed to read response");
    let decrypted = client.decrypt(response).expect("Failed to decrypt message");

    // Print it out and shut the server down.
    let str_message = String::from_utf8_lossy(decrypted.as_slice());
    println!("Server responded: {str_message}");
    drop(request_tx);

    // Wait for server completion, so that the completion message is always printed.
    server_handle.join().expect("failed to join server thread");
}
