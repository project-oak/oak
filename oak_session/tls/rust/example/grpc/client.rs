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

use std::sync::Arc;

use clap::Parser;
use oak_session_tls::{ClientContextConfig, OakSessionTlsClientContext};
use oak_session_tls_example_grpc_proto::oak::session::tls::example::{
    TlsSessionRequest, tls_over_grpc_client::TlsOverGrpcClient,
};
use tokio::sync::Mutex;

#[derive(Parser, Debug)]
struct Args {
    #[arg(long, default_value = "8080")]
    port: String,
    #[arg(long, default_value = "oak_session/tls/testing/test_ca.pem")]
    ca_cert: String,
    #[arg(long, default_value = "oak_session/tls/testing/test_client.key")]
    client_key: String,
    #[arg(long, default_value = "oak_session/tls/testing/test_client.pem")]
    client_cert: String,
    /// Expected server name for SNI and certificate SAN verification.
    #[arg(long, default_value = "oak-session-tls")]
    server_name: String,
}

fn load_cert(path: &str) -> rustls_pki_types::CertificateDer<'static> {
    oak_session_tls::utils::load_cert_der(std::io::BufReader::new(
        std::fs::File::open(path).expect("failed to open cert file"),
    ))
}

fn load_key(path: &str) -> rustls_pki_types::PrivateKeyDer<'static> {
    oak_session_tls::utils::load_key_der(std::io::BufReader::new(
        std::fs::File::open(path).expect("failed to open key file"),
    ))
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let ca_cert = load_cert(&args.ca_cert);
    let client_key = load_key(&args.client_key);
    let client_cert = load_cert(&args.client_cert);

    let config = ClientContextConfig {
        tls_identity_provider: Some(oak_session_tls::utils::create_static_cert_identity_provider(
            client_key,
            client_cert,
        )),
        server_trust_anchor_der: Some(ca_cert),
        custom_cert_verifier: None,
        expected_server_name: Some(args.server_name),
    };

    let client_context = OakSessionTlsClientContext::create(config).unwrap();

    let server_address = format!("http://[::1]:{}", args.port);
    let mut stub = TlsOverGrpcClient::connect(server_address).await?;

    let (tx, rx) = tokio::sync::mpsc::channel(100);
    let request_stream = tokio_stream::wrappers::ReceiverStream::new(rx);

    let response_stream =
        Arc::new(Mutex::new(stub.tls_session(request_stream).await?.into_inner()));

    let (mut session, _initial_data) = client_context
        .new_initialized_session(
            |frame| {
                let tx_send = tx.clone();
                async move {
                    if tx_send.send(TlsSessionRequest { frame }).await.is_err() {
                        return Err(std::io::Error::other("failed to send frame"));
                    }
                    Ok(())
                }
            },
            || {
                let stream = response_stream.clone();
                async move {
                    match stream.lock().await.message().await {
                        Ok(Some(resp)) => Ok(Some(resp.frame)),
                        Ok(None) => Ok(None),
                        Err(e) => Err(std::io::Error::other(e)),
                    }
                }
            },
        )
        .await
        .expect("Client handshake failed");

    println!("Client handshake complete.");

    let message = b"world";
    let encrypted = session.encrypt(message).expect("Failed to encrypt message");

    tx.send(TlsSessionRequest { frame: encrypted }).await.unwrap();

    let mut stream_locked = response_stream.lock().await;
    let mut decrypted = Vec::new();
    // Loop until we receive non-empty application data. session.decrypt may
    // return empty data if it processed a post-handshake TLS control frame
    // (e.g., a session ticket).
    while decrypted.is_empty() {
        let resp = stream_locked.message().await?.expect("No response received");
        decrypted = session.decrypt(&resp.frame).expect("Failed to decrypt message");
    }

    println!("Received: {}", String::from_utf8_lossy(&decrypted));

    println!("Completing session...");
    drop(tx); // Close the request stream

    Ok(())
}
