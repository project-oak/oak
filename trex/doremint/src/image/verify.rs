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

//! Mode which verifies an endorsement.
/**
Sample call:

export IMAGE_REF=example.com/app@sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
bazel run trex/doremint image verify -- \
  --image="$IMAGE_REF" \
  --claims-toml=$(pwd)/trex/doremint/testdata/claims.toml \
  --access-token="$(gcloud auth print-access-token)" \
  --endorser-public-key="$HOME/cosign.pub"
*/
use anyhow::Context;
use clap::Parser;
use cosign_util::pull_package;
use oak_digest::Digest;
use oak_time_std::instant::now;
use oci_client::{Client, client::ClientConfig, secrets::RegistryAuth};
use oci_spec::distribution::Reference;

use crate::flags::{Claims, read_pem_file};

#[derive(Parser, Debug)]
#[command(about = "Verify an endorsement for a container image")]
pub struct VerifyCommand {
    #[arg(from_global)]
    pub image: Reference,

    #[arg(from_global)]
    pub claims: Claims,

    #[arg(long, help = "Identity token for Cloud authentication")]
    pub access_token: Option<String>,

    #[arg(long, value_parser = read_pem_file, help = "Path to a file containing the PEM-encoded public key of the endorser")]
    pub endorser_public_key: String,
}

impl VerifyCommand {
    pub async fn run(&self) -> anyhow::Result<()> {
        let auth = match &self.access_token {
            Some(token) => RegistryAuth::Bearer(token.clone()),
            None => RegistryAuth::Anonymous,
        };
        let client = Client::new(ClientConfig::default());

        let package = pull_package(&client, &auth, &self.image, &self.endorser_public_key).await?;
        let statement = package.verify(now().into_unix_millis())?;

        // Need to verify the endorsement subject and the claims as well.
        let typed_hash = self.image.digest().context("missing digest in OCI reference")?;
        let digest = Digest::from_typed_hash(typed_hash)?;

        let claims_vec = self
            .claims
            .claims_toml
            .as_ref()
            .map(|c| c.claims.clone())
            .or(self.claims.claims.clone())
            .unwrap();
        if claims_vec.is_empty() {
            anyhow::bail!("at least one claim must be provided");
        }

        let claims: Vec<&str> = claims_vec.iter().map(|s| s.as_str()).collect();
        statement
            .validate(Some(digest.into()), now(), &claims)
            .context("validating endorsement statement")?;

        println!("Endorsement verified successfully for image {}", self.image);

        Ok(())
    }
}
