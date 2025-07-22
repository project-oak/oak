//
// Copyright 2024 The Project Oak Authors
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
use serde::Deserialize;

// See https://cloud.google.com/compute/docs/metadata/querying-metadata#metadata_server_endpoints
const METADATA_BASE_URL: &str = "http://metadata.google.internal/computeMetadata/v1";

// See https://cloud.google.com/compute/docs/access/authenticate-workloads#applications
const DEFAULT_TOKEN_PATH: &str = "/instance/service-accounts/default/token";

#[derive(Deserialize)]
pub struct AuthenticationToken {
    access_token: String,
    token_type: String,
}

/// Obtain a bearer token from the Metadata Service for the running VM
pub async fn get_bearer_token() -> anyhow::Result<String> {
    let response_body =
        get_metadata_value(DEFAULT_TOKEN_PATH).await.context("failed to fetch token")?;
    let response: AuthenticationToken =
        serde_json::from_str(&response_body).context("failed to parse token response")?;

    match response.token_type.as_str() {
        "Bearer" => Ok(response.access_token),
        other => Err(anyhow::anyhow!("unexpected token type: {other}")),
    }
}

/// Fetches a value from the GCP metadata server.
///
/// See https://cloud.google.com/compute/docs/metadata/querying-metadata#programmatically-query-metadata
pub async fn get_metadata_value(path: &str) -> anyhow::Result<String> {
    let client = reqwest::Client::new();
    let url = format!("{METADATA_BASE_URL}/{path}");

    let response = client
        .get(&url)
        // Setting this header is required to prevent accidental metadata queries or something.
        // See https://cloud.google.com/compute/docs/metadata/querying-metadata#parts-of-a-request
        .header("Metadata-Flavor", "Google")
        .send()
        .await
        .with_context(|| format!("failed to fetch metadata from {url}"))?;

    if !response.status().is_success() {
        let status = response.status();
        let error_message = response.text().await.unwrap_or_default();
        return Err(anyhow::anyhow!(
            "metadata server at {url} returned status {status} with body {error_message}"
        ));
    }

    response.text().await.context("failed to read metadata response")
}
