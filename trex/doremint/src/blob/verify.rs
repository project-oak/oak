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

use anyhow::Result;
use clap::Parser;
use digest_util::hex_digest_from_typed_hash;
use oak_proto_rust::oak::HexDigest;
use oak_time::Instant;
use trex_client::{
    http::{fetch_index, HttpBlobFetcher, HttpEndorsementIndex},
    EndorsementVerifier,
};

use crate::flags;

#[derive(Parser, Debug)]
pub struct Verify {
    #[arg(long, help = "URL to the root of the OCI endorsement repository")]
    http_index_prefix: String,

    #[arg(long, help = "Expected OIDC issuer for the cosign identity")]
    cosign_oidc_issuer: String,

    #[arg(long, help = "Expected email identity of the endorser")]
    cosign_identity: String,

    #[arg(
        long,
        help = "Timestamp to check validity at (RFC3339). Defaults to now.",
        value_parser = flags::parse_current_time,
        default_value = ""
    )]
    valid_at: Instant,

    #[command(flatten)]
    pub claims: flags::Claims,

    #[arg(long, help = "Digest of the subject to verify (e.g., sha256:...)")]
    subject_digest: String,
}

impl Verify {
    pub async fn run(&self) -> Result<()> {
        let subject_digest: HexDigest = hex_digest_from_typed_hash(&self.subject_digest)?;

        let image_index = fetch_index(&self.http_index_prefix).await?;

        let index = Box::new(HttpEndorsementIndex::new(Box::new(move || image_index.clone())));
        let fetcher = Box::new(HttpBlobFetcher::new(self.http_index_prefix.clone()));

        let verifier = EndorsementVerifier::new(index, fetcher);

        let required_claims = self
            .claims
            .claims_toml
            .as_ref()
            .map(|c| c.claims.clone())
            .or(self.claims.claims.clone())
            .unwrap_or_default();

        println!("Verifying endorsement for subject {}", self.subject_digest);
        let statement = verifier
            .verify(
                &subject_digest,
                self.valid_at,
                &required_claims,
                &self.cosign_identity,
                &self.cosign_oidc_issuer,
            )
            .await?;

        println!("Verification successful!");
        println!("Endorsement details:");
        println!("  Issued on: {}", statement.predicate.issued_on);
        if let Some(validity) = statement.predicate.validity {
            println!("  Valid from: {}", validity.not_before);
            println!("  Valid until: {}", validity.not_after);
        }
        println!("  Claims verified:");
        for claim in &required_claims {
            println!("    - {}", claim);
        }

        Ok(())
    }
}
