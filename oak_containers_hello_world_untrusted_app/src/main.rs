//
// Copyright 2023 The Project Oak Authors
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

use anyhow::Context;
use clap::Parser;
use oak_client::verifier::{AttestationVerifier, InsecureAttestationVerifier};
use oak_crypto::encryptor::ClientEncryptor;

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    let args = oak_containers_launcher::Args::parse();
    env_logger::init();

    let mut untrusted_app = oak_containers_hello_world_untrusted_app::UntrustedApp::create(args)
        .await
        .map_err(|error| anyhow::anyhow!("couldn't create untrusted app: {}", error))?;

    let endorsed_evidence = untrusted_app
        .get_endorsed_evidence()
        .await
        .map_err(|error| anyhow::anyhow!("couldn't get endorsed evidence: {}", error))?;
    let evidence = endorsed_evidence.evidence.context("no evidence provided")?;
    let endorsements = endorsed_evidence.endorsements.context("no endorsements provided")?;

    let attestation_verifier = InsecureAttestationVerifier {};
    let attestation_results = attestation_verifier
        .verify(&evidence, &endorsements)
        .context("couldn't verify endorsed evidence")?;

    let mut client_encryptor = ClientEncryptor::create(&attestation_results.encryption_public_key)
        .context("couldn't create client encryptor")?;
    let encrypted_request = client_encryptor
        .encrypt("Untrusted App".as_bytes(), EMPTY_ASSOCIATED_DATA)
        .context("couldn't encrypt request")?;

    let encrypted_response = untrusted_app
        .hello(encrypted_request)
        .await
        .map_err(|error| anyhow::anyhow!("couldn't get encrypted response: {}", error))?;

    let (response, _) =
        client_encryptor.decrypt(&encrypted_response).context("couldn't decrypt response")?;
    let greeting = String::from_utf8(response).expect("couldn't parse response");

    log::info!("Received a greeting from the trusted app: {:?}", greeting);

    Ok(())
}
