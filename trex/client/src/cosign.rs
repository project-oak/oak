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

//! Wrappers around the [`cosign`](https://docs.sigstore.dev/cosign/overview/)
//! CLI for blob signing and verification.
//!
//! Both [`cosign_verify_blob`] and [`cosign_sign_blob`] shell out to the
//! `cosign` binary, writing inputs to temporary files and collecting outputs.
//! A `cosign` binary must be available on `$PATH` at runtime.

use std::{
    fmt, fs,
    process::{Command, Stdio},
    str::FromStr,
};

use anyhow::{Context, Result, anyhow};
use tempfile::NamedTempFile;

/// Controls the Fulcio OIDC authentication flow used by cosign for keyless
/// signing.
///
/// This mirrors cosign's `--fulcio-auth-flow` flag. See
/// <https://docs.sigstore.dev/cosign/signing/overview/> for details.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FulcioAuthFlow {
    /// Opens a browser for interactive OAuth login. Suitable for local
    /// developer use where a human is present.
    Browser,
    /// Uses ambient OIDC credentials (e.g., GCP workload identity,
    /// `GOOGLE_APPLICATION_CREDENTIALS`). Suitable for CI and test
    /// environments where no browser is available.
    Token,
}

impl fmt::Display for FulcioAuthFlow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FulcioAuthFlow::Browser => write!(f, "browser"),
            FulcioAuthFlow::Token => write!(f, "token"),
        }
    }
}

impl FromStr for FulcioAuthFlow {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s {
            "browser" => Ok(FulcioAuthFlow::Browser),
            "token" => Ok(FulcioAuthFlow::Token),
            other => {
                Err(format!("invalid fulcio auth flow '{other}', expected 'browser' or 'token'"))
            }
        }
    }
}

/// Verifies a blob and its signature bundle using the `cosign` CLI.
pub fn cosign_verify_blob(
    cert_identity: &str,
    cert_oidc_issuer: &str,
    bundle_bytes: &[u8],
    blob_bytes: &[u8],
) -> Result<()> {
    // Write endorsement and bundle to temporary files for cosign CLI.
    let mut blob_file = NamedTempFile::new().context("creating temp blob file")?;
    std::io::Write::write_all(&mut blob_file, blob_bytes).context("writing blob to temp file")?;

    let mut bundle_file = NamedTempFile::new().context("creating temp bundle file")?;
    std::io::Write::write_all(&mut bundle_file, bundle_bytes)
        .context("writing bundle to temp file")?;

    let mut command = Command::new("cosign");
    command
        .arg("verify-blob")
        .arg(format!("--certificate-identity={cert_identity}"))
        .arg(format!("--certificate-oidc-issuer={cert_oidc_issuer}"))
        .arg(format!("--bundle={}", bundle_file.path().display()))
        .arg(blob_file.path());

    let output = command.output().context("running cosign CLI")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(anyhow!("cosign verification failed: {}", stderr));
    }

    Ok(())
}

/// Signs a blob using the `cosign` CLI.
///
/// This function uses keyless signing via Sigstore's Fulcio CA. It requires
/// OIDC credentials to be available in the environment (e.g., via GCP workload
/// identity, `GOOGLE_APPLICATION_CREDENTIALS`, or `gcloud auth
/// application-default login`).
///
/// # Arguments
///
/// * `blob_bytes` - The blob data to sign.
/// * `fulcio_auth_flow` - Controls the OIDC authentication method.
///   [`FulcioAuthFlow::Browser`] opens a browser for interactive OAuth;
///   [`FulcioAuthFlow::Token`] uses only ambient credentials and fails fast if
///   none are available (suitable for CI/test environments).
pub fn cosign_sign_blob(blob_bytes: &[u8], fulcio_auth_flow: FulcioAuthFlow) -> Result<Vec<u8>> {
    let mut blob_file = NamedTempFile::new().context("creating temp blob file")?;
    std::io::Write::write_all(&mut blob_file, blob_bytes).context("writing blob to temp file")?;

    let temp_bundle_path = std::env::temp_dir().join(format!("bundle-{}.json", std::process::id()));

    let mut command = Command::new("cosign");
    command
        .arg("sign-blob")
        .arg("--yes")
        .arg(format!("--bundle={}", temp_bundle_path.display()))
        .arg(blob_file.path());

    command.arg(format!("--fulcio-auth-flow={fulcio_auth_flow}"));

    match fulcio_auth_flow {
        FulcioAuthFlow::Browser => {
            command.stderr(Stdio::inherit());
        }
        FulcioAuthFlow::Token => {
            command
                // Close stdin to prevent any interactive prompts from blocking.
                .stdin(Stdio::null())
                // Capture stderr so we can provide a better error message.
                .stderr(Stdio::piped());
        }
    }

    let output = command.output().context("failed to execute cosign")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        // Provide a helpful error message for the common case of missing credentials.
        if fulcio_auth_flow == FulcioAuthFlow::Token
            && (stderr.contains("no identity token") || stderr.contains("could not find"))
        {
            return Err(anyhow!(
                "cosign signing failed: no OIDC credentials available.\n\
                 To fix this, either:\n\
                 - Run `gcloud auth application-default login` to authenticate, or\n\
                 - Set GOOGLE_APPLICATION_CREDENTIALS to a service account key file, or\n\
                 - Run in an environment with workload identity (e.g., GCP CI)\n\n\
                 Original error: {}",
                stderr
            ));
        }
        return Err(anyhow!("cosign signing failed: {}", stderr));
    }

    fs::read(&temp_bundle_path).context("reading generated bundle")
}
