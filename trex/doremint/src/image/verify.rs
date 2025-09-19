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

use anyhow::Context;
use clap::Parser;
use digest_util::hex_digest_from_typed_hash;
use intoto::statement::parse_statement;
use oak_time_std::instant::now;
use oci_client::{client::ClientConfig, secrets::RegistryAuth, Client};
use oci_spec::distribution::Reference;
use p256::{ecdsa::VerifyingKey, pkcs8::DecodePublicKey};
use rekor::{
    get_rekor_v1_public_key_raw,
    log_entry::{verify_rekor_log_entry_ecdsa, LogEntry},
};
use sigstore_client::cosign;

use crate::flags::{verifying_key_parser, Claims};

#[derive(Parser, Debug)]
#[command(about = "Verify an endorsement for a container image")]
pub struct VerifyCommand {
    #[arg(from_global)]
    pub image: Reference,

    #[arg(from_global)]
    pub claims: Claims,

    #[arg(long, help = "Identity token for Cloud authentication")]
    pub access_token: Option<String>,

    #[arg(long, value_parser = verifying_key_parser, help = "Path to a file containing the PEM-encoded public key of the endorser")]
    pub endorser_public_key: Vec<u8>,
}

impl VerifyCommand {
    pub async fn run(&self) -> anyhow::Result<()> {
        let auth = match &self.access_token {
            Some(token) => RegistryAuth::Bearer(token.clone()),
            None => RegistryAuth::Anonymous,
        };
        let client = Client::new(ClientConfig::default());

        // TODO: b/445140472 - Turn this all into a call to //tr/verify_endorsement.
        let (endorsement, bundle) = cosign::pull_payload(&client, &auth, &self.image).await?;

        let endorser_verifying_key =
            VerifyingKey::from_public_key_der(&self.endorser_public_key)
                .map_err(|e| anyhow::anyhow!("failed to parse public key: {}", e))?;
        let endorsement = endorsement
            .verify(&endorser_verifying_key)
            .context("verifying endorsement signature")?;

        // Verify the Rekor log entry.
        let log_entry = LogEntry::from_cosign_bundle(bundle)?;
        let serialized_log_entry = serde_json::to_vec(&log_entry)?;
        let parsed_log_entry = verify_rekor_log_entry_ecdsa(
            &serialized_log_entry,
            &get_rekor_v1_public_key_raw(),
            endorsement.message(),
        )
        .context("verifying Rekor log entry")?;
        parsed_log_entry.compare_public_key(&self.endorser_public_key)?;

        // Verify the endorsement statement.
        let statement = parse_statement(endorsement.message())?;
        let typed_hash = self.image.digest().context("missing digest in OCI reference")?;
        let digest = hex_digest_from_typed_hash(typed_hash)?;
        // Convert Vec<String> to Vec<&str>.
        let claims: Vec<&str> = self.claims.claims.iter().map(|s| s.as_str()).collect();
        statement
            .validate(Some(digest), now(), &claims)
            .context("validating endorsement statement")?;

        println!("Endorsement verified successfully for image {}", self.image);

        Ok(())
    }
}
