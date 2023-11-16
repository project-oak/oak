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
//

//! Verifies binary endorsements as coming from Transparent Release.

use anyhow::Context;
use base64::{prelude::BASE64_STANDARD, Engine as _};
use oak_transparency_claims::claims::{
    parse_endorsement_statement, validate_endorsement, verify_validity_duration,
};

use crate::{
    rekor::{get_rekor_log_entry_body, verify_rekor_log_entry},
    util::{convert_pem_to_raw, equal_keys},
};

/// Verifies the binary endorsement for a given measurement.
pub fn verify_binary_endorsement(
    now_utc_millis: i64,
    endorsement: &[u8],
    log_entry: &[u8],
    binary_digest: &[u8],
    binary_digest_alg: &str,
    endorser_public_key: &[u8],
    rekor_public_key: &[u8],
) -> anyhow::Result<()> {
    verify_endorsement_statement(
        now_utc_millis,
        endorsement,
        binary_digest,
        binary_digest_alg,
    )?;
    verify_rekor_log_entry(log_entry, rekor_public_key, endorsement)?;
    verify_endorser_public_key(log_entry, endorser_public_key)?;

    Ok(())
}

/// Verifies endorsement against the given reference values.
pub fn verify_endorsement_statement(
    now_utc_millis: i64,
    endorsement: &[u8],
    binary_digest: &[u8],
    binary_digest_alg: &str,
) -> anyhow::Result<()> {
    let claim = parse_endorsement_statement(endorsement)?;
    if let Err(err) = validate_endorsement(&claim) {
        anyhow::bail!("validating endorsement: {err:?}");
    }
    verify_validity_duration(now_utc_millis, &claim)?;
    if claim.subject.len() != 1 {
        anyhow::bail!(
            "expected 1 subject in the endorsement, found {}",
            claim.subject.len()
        );
    }

    let binary_digest = core::str::from_utf8(binary_digest)?;
    match claim.subject[0].digest.get(binary_digest_alg) {
        Some(found_digest) => {
            if found_digest != binary_digest {
                anyhow::bail!(
                    "unexpected binary {} digest: expected {}, got {}",
                    binary_digest_alg,
                    binary_digest,
                    found_digest
                )
            }
        }
        None => anyhow::bail!("missing {binary_digest_alg} digest in the endorsement statement"),
    }

    Ok(())
}

/// Verifies that the endorser public key coincides with the one contained in the attestation.
pub fn verify_endorser_public_key(
    log_entry: &[u8],
    endorser_public_key: &[u8],
) -> anyhow::Result<()> {
    // TODO(#4231): Currently, we only check that the public keys are the same. Should be updated to
    // support verifying rolling keys.

    let body = get_rekor_log_entry_body(log_entry)?;

    let actual_pem_vec = BASE64_STANDARD
        .decode(body.spec.signature.public_key.content)
        .context("couldn't base64-decode public key bytes from server")?;
    let actual_pem = core::str::from_utf8(&actual_pem_vec)?;
    let actual = convert_pem_to_raw(actual_pem)?;

    if !equal_keys(endorser_public_key, &actual)? {
        anyhow::bail!(
            "endorser public key mismatch: expected {:?} found {:?}",
            endorser_public_key,
            actual,
        )
    }

    Ok(())
}
