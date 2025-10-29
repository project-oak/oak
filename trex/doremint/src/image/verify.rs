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
  --image "$IMAGE_REF" \
  --claims $(pwd)/trex/doremint/testdata/claims.toml \
  --access-token "$(gcloud auth print-access-token)" \
  --endorser-public-key "$HOME/cosign.pub"
*/
use anyhow::Context;
use clap::Parser;
use digest_util::hex_digest_from_typed_hash;
use oak_time_std::instant::now;
use oci_client::{client::ClientConfig, secrets::RegistryAuth, Client};
use oci_spec::distribution::Reference;
use rekor::{
    get_rekor_v1_public_key_raw,
    log_entry::{serialize_rekor_log_entry, LogEntry},
};
use sigstore_client::cosign;
use verify_endorsement::{
    create_endorsement_reference_value, create_signed_endorsement, create_verifying_key_from_pem,
    create_verifying_key_from_raw, verify_endorsement,
};

use crate::flags::{read_pem_file, Claims};

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

        let (statement, rekor_bundle) = cosign::pull_payload(&client, &auth, &self.image).await?;

        let log_entry = LogEntry::from_cosign_bundle(rekor_bundle.raw_data())?;
        let serialized_log_entry = serialize_rekor_log_entry(&log_entry)?;
        println!("Converted Rekor log entry: {serialized_log_entry:?}");

        let signed_endorsement = create_signed_endorsement(
            statement.unverified_message(),
            statement.signature(),
            0,   // The key ID is not used here.
            &[], // The subject is not needed for verification.
            &serialized_log_entry,
        );

        let endorser_key = create_verifying_key_from_pem(&self.endorser_public_key, 0);
        let rekor_key = create_verifying_key_from_raw(&get_rekor_v1_public_key_raw(), 0);
        let ref_value = create_endorsement_reference_value(endorser_key, Some(rekor_key));

        let statement =
            verify_endorsement(now().into_unix_millis(), &signed_endorsement, &ref_value)?;

        // Need to verify the endorsement subject and the claims as well.
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
