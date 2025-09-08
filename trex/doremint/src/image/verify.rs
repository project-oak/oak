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
use chrono::Utc;
use clap::Parser;
use intoto::statement::parse_statement;
use oak_time::Instant;
use oci_client::{client::ClientConfig, secrets::RegistryAuth, Client};
use oci_spec::distribution::Reference;
use p256::{ecdsa::VerifyingKey, pkcs8::DecodePublicKey};
use sigstore::rekor::{
    from_cosign_bundle,
    hashedrekord::{HashedRekord, Unverified},
    RekorPayload,
};
use sigstore_client::cosign;

use crate::{flags, flags::oci_ref_to_hex_digest};

const REKOR_PUBLIC_KEY_PEM: &str = include_str!("../../data/rekor_public_key.pem");

#[derive(Parser, Debug)]
#[command(about = "Verify an endorsement for a container image")]
pub struct VerifyCommand {
    #[arg(from_global)]
    pub image: Reference,

    #[arg(from_global)]
    pub claims: flags::Claims,

    #[arg(long, help = "Identity token for Cloud authentication")]
    pub access_token: Option<String>,

    #[arg(long, value_parser = flags::verifying_key_parser, help = "Path to a file containing the PEM-encoded public key of the endorser")]
    pub endorser_public_key: VerifyingKey,
}

impl VerifyCommand {
    pub async fn run(&self) -> anyhow::Result<()> {
        let rekor_public_key = VerifyingKey::from_public_key_pem(REKOR_PUBLIC_KEY_PEM)
            .map_err(|e| anyhow::anyhow!("failed to parse rekor public key: {}", e))?;

        let auth = match &self.access_token {
            Some(token) => RegistryAuth::Bearer(token.clone()),
            None => RegistryAuth::Anonymous,
        };
        let client = Client::new(ClientConfig::default());

        let (endorsement, bundle) = cosign::pull_payload(&client, &auth, &self.image).await?;

        let endorsement = endorsement
            .verify(&self.endorser_public_key)
            .context("verifying endorsement signature")?;

        let rekor = from_cosign_bundle(bundle)?;
        let rekor = rekor.verify(&rekor_public_key).context("verifying rekor signature")?;
        let rekor: RekorPayload = serde_json::from_slice(rekor.message())?;
        let hashed_rekord: HashedRekord<Unverified> = rekor.payload_body()?;
        hashed_rekord
            .verify(&self.endorser_public_key, endorsement.message())
            .context("verifying Rekor log entry")?;

        let statement = parse_statement(endorsement.message())?;
        let now = Instant::from(Utc::now());
        let digest = oci_ref_to_hex_digest(&self.image)?;
        // Convert Vec<String> to Vec<&str>.
        let claims: Vec<&str> = self.claims.claims.iter().map(|s| s.as_str()).collect();
        statement
            .validate(Some(digest), now, &claims)
            .context("validating endorsement statement")?;

        println!("Endorsement verified successfully for image {}", self.image);

        Ok(())
    }
}
