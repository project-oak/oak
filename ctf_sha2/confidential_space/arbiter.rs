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

#![feature(try_blocks)]

use arbiter_rust_proto::oak::ctf_sha2::arbiter::{arbiter_input::TeeProof, ArbiterInput};
use clap::Parser;
use jwt::{Token, Unverified};
use log::{error, info};
use oak_attestation_gcp::{
    jwt::{verification::report_attestation_token, Claims, Header},
    CONFIDENTIAL_SPACE_ROOT_CERT_PEM,
};
use prost::Message;
use sha2::{Digest, Sha256};
use x509_cert::{der::DecodePem, Certificate};

// See ctf_sha2/src/main.rs.
const OAK_CTF_SHA2_AUDIENCE: &str = "z08381475938604996746";

// Built at commit c9c0b847ea9e349ab8c8b797bab5e03d1762cb89:
// $ git checkout c9c0b847ea9e349ab8c8b797bab5e03d1762cb89 && \
//       bazel run ctf_sha2:image_push
const EXPECTED_WORKLOAD_DIGEST: &str =
    "sha256:692ab39ff6bd177481546e39179d40b961c2b5de7959f0ee388806050ac0244c";

fn main() -> anyhow::Result<()> {
    env_logger::init();

    let root_certificate =
        Certificate::from_pem(CONFIDENTIAL_SPACE_ROOT_CERT_PEM).map_err(anyhow::Error::msg)?;
    falsify::falsify(falsify::FalsifyArgs::parse(), |input| {
        let input = match ArbiterInput::decode(input.as_slice()) {
            Ok(input) => input,
            Err(e) => {
                error!("Input failed to decode: {e}");
                return;
            }
        };

        let tee_proof = match input.tee_proof {
            Some(tee_proof) => tee_proof,
            None => {
                error!("Input does not contain tee_proof");
                return;
            }
        };

        let confidential_space_jwt = match tee_proof {
            TeeProof::ConfidentialSpaceJwt(confidential_space_jwt) => confidential_space_jwt,
            _ => {
                error!("Input does not contain confidential_space_jwt");
                return;
            }
        };

        let parsed_token =
            match Token::<Header, Claims, Unverified>::parse_unverified(&confidential_space_jwt) {
                Ok(parsed_token) => parsed_token,
                Err(e) => {
                    error!("Failed to parse JWT: {e}");
                    return;
                }
            };

        // Here we trust the JWT issuance timestamp. This is a bit circular, but there
        // is no obvious better alternative which results in deterministic behaviour.
        let now = parsed_token.claims().issued_at;
        let verified_token = match report_attestation_token(
            parsed_token,
            &root_certificate,
            &now,
            OAK_CTF_SHA2_AUDIENCE.to_string(),
        )
        .into_checked_token()
        {
            Ok(verified_token) => verified_token,
            Err(e) => {
                info!("Failed to verify JWT: {e}");
                return;
            }
        };

        let image_reference = match verified_token.claims().effective_reference() {
            Ok(image_reference) => image_reference,
            Err(e) => {
                error!("Failed to get image reference: {e}");
                return;
            }
        };

        // Built at commit c9c0b847ea9e349ab8c8b797bab5e03d1762cb89:
        // $ git checkout c9c0b847ea9e349ab8c8b797bab5e03d1762cb89 && \
        //       bazel run ctf_sha2:image_push
        if image_reference.digest() != Some(EXPECTED_WORKLOAD_DIGEST) {
            info!(
                "Unexpected workload digest: wanted {:?} but got {:?}",
                Some(EXPECTED_WORKLOAD_DIGEST),
                image_reference.digest()
            );
            return;
        }
        assert_ne!(
            compute_expected_flag_digest_string(&input.flag),
            verified_token.claims().eat_nonce
        );
    });
    Ok(())
}

fn compute_expected_flag_digest_string(flag: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(flag);
    let expected_flag_digest = hasher.finalize();
    format!("{expected_flag_digest:x}")
}
