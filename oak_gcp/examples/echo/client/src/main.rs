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

//! Sends a string to the enclave app and prints the return.

use std::sync::Arc;

use anyhow::Context;
use clap::Parser;
use oak_proto_rust::oak::attestation::v1::{
    CollectedAttestation, collected_attestation::RequestMetadata,
};
use oak_session::session::{AttestationEvidence, AttestationPublisher};
use oak_time_std::clock::SystemTimeClock;
use p256::{ecdsa::VerifyingKey, pkcs8::DecodePublicKey};
use prost::Message;

#[derive(Parser, Clone)]
#[command(about = "Oak Echo Client")]
pub struct Opt {
    #[arg(
        long,
        help = "URI of the Echo enclave application to connect to",
        default_value = "http://localhost:8080"
    )]
    uri: String,

    #[arg(long, help = "The message to send to the enclave application")]
    request: Option<String>,

    #[arg(long, help = "A path where the server's evidence will be written to")]
    server_evidence_output_path: Option<String>,

    #[arg(long, help = "A path to the developer's public key")]
    developer_public_key: String,
}

// Implementation of the [`AttestationPublisher`] that stores the evidence
// received from the server in the file specified by the user, for debugging
// purposes.
pub struct GcpAttestationPublisher {
    path: String,
    metadata: RequestMetadata,
}

impl AttestationPublisher for GcpAttestationPublisher {
    fn publish(&self, evidence: AttestationEvidence) {
        let output = CollectedAttestation {
            request_metadata: Some(self.metadata.clone()),
            endorsed_evidence: evidence.evidence,
            session_bindings: evidence.evidence_bindings,
            handshake_hash: evidence.handshake_hash,
        };
        std::fs::write(self.path.clone(), output.encode_to_vec())
            .expect("failed to write out the evidence");
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::parse();

    let developer_public_key = std::fs::read_to_string(&opt.developer_public_key)?;
    let developer_public_key = VerifyingKey::from_public_key_pem(&developer_public_key)
        .map_err(|e| anyhow::anyhow!("failed to parse public key: {e}"))?;

    let publisher: Option<Arc<dyn AttestationPublisher>> = match opt.server_evidence_output_path {
        Some(path) => Some(Arc::new(GcpAttestationPublisher {
            path,
            metadata: RequestMetadata { uri: opt.uri.clone(), request_time: None },
        })),
        None => None,
    };

    let mut client = oak_gcp_examples_echo_client::EchoClient::create(
        &opt.uri,
        Arc::new(SystemTimeClock {}),
        developer_public_key,
        publisher,
    )
    .await
    .context("couldn't connect to server")?;

    if let Some(request) = opt.request {
        println!("Request: {request}");
        let decrypted_response = String::from_utf8(
            client.echo(request.as_bytes()).await.context("couldn't send request")?,
        )
        .context("response is not valid UTF-8")?;
        println!("Response: {decrypted_response}");
    } else {
        for line in std::io::stdin().lines() {
            let decrypted_response = String::from_utf8(
                client
                    .echo(line.context("invalid line")?.as_bytes())
                    .await
                    .context("couldn't send request")?,
            )
            .context("response is not valid UTF-8")?;
            println!("{decrypted_response}");
        }
    }

    Ok(())
}
