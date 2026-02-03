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

use std::{
    fs,
    process::{Command, Stdio},
};

use anyhow::{Context, Result, anyhow};
use tempfile::NamedTempFile;

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
pub fn cosign_sign_blob(blob_bytes: &[u8]) -> Result<Vec<u8>> {
    let mut blob_file = NamedTempFile::new().context("creating temp blob file")?;
    std::io::Write::write_all(&mut blob_file, blob_bytes).context("writing blob to temp file")?;

    let temp_bundle_path = std::env::temp_dir().join(format!("bundle-{}.json", std::process::id()));

    let mut command = Command::new("cosign");
    command
        .arg("sign-blob")
        .arg("--yes")
        .arg(format!("--bundle={}", temp_bundle_path.display()))
        .arg(blob_file.path())
        .stderr(Stdio::inherit());

    command.status().context("failed to execute cosign")?.exit_ok()?;

    fs::read(&temp_bundle_path).context("failed to read generated bundle")
}
