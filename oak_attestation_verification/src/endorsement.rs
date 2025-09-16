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

//! TODO: b/379253152 - Entire module is deprecated and will be removed.

use anyhow::Context;
use base64::{prelude::BASE64_STANDARD, Engine as _};
use intoto::statement::parse_statement;
use key_util::{convert_pem_to_raw, equal_keys, verify_signature_ecdsa};
use oak_time::Instant;
use rekor::log_entry::{
    parse_rekor_log_entry, parse_rekor_log_entry_body, verify_rekor_log_entry_ecdsa,
};

/// Verifies the binary endorsement against log entry and public keys.
///
/// `endorser_public_key` and `signature` must be present.
///
/// If `rekor_public_key` is present, then presence of the log entry is
/// required and the log entry will be verified. If `rekor_public_key`
/// is empty (not set), then verification is skipped no matter if the log
/// entry is present or not.
pub(crate) fn verify_binary_endorsement(
    now_utc_millis: i64,
    endorsement: &[u8],
    signature: &[u8],
    log_entry: &[u8],
    endorser_public_key: &[u8],
    rekor_public_key: &[u8],
) -> anyhow::Result<()> {
    if signature.is_empty() {
        anyhow::bail!("signature of endorsement is required");
    }
    if endorser_public_key.is_empty() {
        anyhow::bail!("endorser's public key is required");
    }

    // The signature verification is also part of log entry verification,
    // so in some cases this check will be dispensable. We verify the
    // signature nonetheless before parsing the endorsement.
    verify_signature_ecdsa(signature, endorsement, endorser_public_key)
        .context("verifying signature")?;

    let statement = parse_statement(endorsement).context("parsing endorsement statement")?;
    let current_time = Instant::from_unix_millis(now_utc_millis);
    statement.validate(None, current_time, &[]).context("validating endorsement statement")?;

    if !rekor_public_key.is_empty() {
        if log_entry.is_empty() {
            anyhow::bail!("log entry unavailable but verification was requested");
        }
        verify_rekor_log_entry_ecdsa(log_entry, rekor_public_key, endorsement)
            .context("verifying rekor log entry")?;
        verify_endorser_public_key_ecdsa(log_entry, endorser_public_key)
            .context("verifying endorser public key")?;
    }

    Ok(())
}

/// Verifies that the endorser public key coincides with the one contained in
/// the attestation.
fn verify_endorser_public_key_ecdsa(
    serialized_log_entry: &[u8],
    endorser_public_key: &[u8],
) -> anyhow::Result<()> {
    // TODO(#4231): Currently, we only check that the public keys are the same.
    // Should be updated to support verifying rolling keys.
    let log_entry = parse_rekor_log_entry(serialized_log_entry)?;
    let body = parse_rekor_log_entry_body(&log_entry).context("getting rekor log entry body")?;

    let actual_pem_vec =
        BASE64_STANDARD.decode(body.spec.signature.public_key.content).map_err(|error| {
            anyhow::anyhow!("couldn't base64-decode public key bytes from server: {}", error)
        })?;
    let actual_pem =
        core::str::from_utf8(&actual_pem_vec).map_err(|error| anyhow::anyhow!(error))?;
    let actual = convert_pem_to_raw(actual_pem)
        .map_err(|e| anyhow::anyhow!(e))
        .context("converting public key from log entry body")?;

    if !equal_keys(endorser_public_key, &actual)? {
        anyhow::bail!(
            "endorser public key mismatch: expected {:?} found {:?}",
            endorser_public_key,
            actual,
        )
    }

    Ok(())
}

#[cfg(test)]
mod tests;
