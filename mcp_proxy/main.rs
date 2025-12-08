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
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context, Result};
use axum::{
    body::Body,
    extract::{Request, State},
    http::StatusCode,
    response::Response,
    routing::any,
    Router,
};
use clap::Parser;
use config::{Config, Filter};
use digest::{compute_canonical_digest, Digest};
use oci_spec::image::ImageIndex;
use thiserror::Error;
use tokio::net::TcpListener;

mod config;
mod digest;

#[derive(Error, Debug)]
pub enum VerificationError {
    #[error("index lookup failed: {0}")]
    IndexLookupFailed(String),
    #[error("endorsement not found in index for subject: {0}")]
    EndorsementNotFound(String),
    #[error("invalid endorsement digest format: {0}")]
    InvalidDigestFormat(String),
    #[error("failed to fetch endorsement blob: {0}")]
    BlobFetchFailed(String),
    #[error("endorsement digest mismatch")]
    DigestMismatch,
    #[error("failed to cache endorsement: {0}")]
    CacheFailed(String),
    #[error("cosign verification failed: {0}")]
    CosignFailed(String),
    #[error("internal error: {0}")]
    Internal(String),
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long, default_value = "config.toml")]
    config: String,
}

#[derive(Clone)]
struct AppState {
    config: Config,
    client: reqwest::Client,
}

/// Entry point for the application. Initializes the logger, parses arguments,
/// loads configuration, sets up the application state, and starts the TCP
/// listener and server.
#[tokio::main]
async fn main() -> Result<()> {
    env_logger::init();
    let args = Args::parse();

    let config_content = fs::read_to_string(&args.config)
        .with_context(|| format!("Failed to read config file: {}", args.config))?;
    let config: Config =
        toml::from_str(&config_content).with_context(|| "Failed to parse config file")?;

    if config.target_mcp_server_url.is_empty() {
        anyhow::bail!("target_mcp_server_url must be provided in config");
    }

    let state = AppState { config: config.clone(), client: reqwest::Client::new() };

    let app = Router::new()
        .route("/", any(handle_request))
        .route("/*path", any(handle_request))
        .with_state(state);

    let addr = "0.0.0.0:8080";
    println!("Starting proxy server on {}", addr);
    let listener = TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    Ok(())
}

/// Handles incoming HTTP requests. Forwards requests to the target MCP server,
/// handles headers, and optionally verifies responses based on configuration
/// filters.
async fn handle_request(
    State(state): State<AppState>,
    req: Request,
) -> Result<Response, (StatusCode, String)> {
    let (parts, body) = req.into_parts();
    let path = parts.uri.path();
    log::info!("Received request: {} {}", parts.method, path);

    // Read all the request body.
    let body_bytes = axum::body::to_bytes(body, usize::MAX).await.map_err(|e| {
        let msg = format!("Failed to read request body: {e}");
        log::error!("{msg}");
        (StatusCode::INTERNAL_SERVER_ERROR, msg)
    })?;

    let mut method = None;
    if !body_bytes.is_empty() {
        if let Ok(json_req) = serde_json::from_slice::<serde_json::Value>(&body_bytes) {
            log::debug!("Parsed Request Body: {json_req:?}");
            if let Some(m) = json_req.get("method").and_then(|v| v.as_str()) {
                method = Some(m.to_string());
                log::info!("Extracted MCP method: {m}");
            }
        } else {
            log::warn!("Request body not JSON or malformed");
        }
    }

    let path_query = parts.uri.path_and_query().map(|pq| pq.as_str()).unwrap_or(parts.uri.path());
    let target_base = state.config.target_mcp_server_url.trim_end_matches('/');
    let target_uri_str = format!("{}{}", target_base, path_query);
    log::info!("Forwarding to target URL: {target_uri_str}");

    let target_url = reqwest::Url::parse(&target_uri_str).map_err(|e| {
        let msg = format!("Invalid target URL: {e}");
        log::error!("{msg}");
        (StatusCode::INTERNAL_SERVER_ERROR, msg)
    })?;

    let mut req_builder = state.client.request(parts.method.clone(), target_url.clone());

    // Copy headers, excluding Host which is set by reqwest based on URL,
    // and hop-by-hop headers that shouldn't be forwarded or are managed by reqwest.
    for (name, value) in &parts.headers {
        match name.as_str() {
            "host" | "content-length" | "transfer-encoding" | "connection" => continue,
            _ => {
                req_builder = req_builder.header(name, value);
            }
        }
    }

    req_builder = req_builder.body(body_bytes.clone());

    let response = req_builder.send().await.map_err(|e| {
        let msg = format!("Failed to forward request: {}", e);
        log::error!("{}", msg);
        (StatusCode::BAD_GATEWAY, msg)
    })?;

    log::info!("Received response from target: {}", response.status());

    let matched_filter = state.config.filters.iter().find(|f| Some(&f.method) == method.as_ref());

    if let Some(filter) = matched_filter {
        log::info!("Request matched filter for method: {}", filter.method);
        if filter.cosign_identity.is_some() {
            return handle_filtered_response(response, filter, &state).await;
        }
    }

    let status = response.status();

    let mut headers = response.headers().clone();

    // Strip headers that might conflict with the new body/stream
    headers.remove(axum::http::header::CONTENT_LENGTH);
    headers.remove(axum::http::header::CONTENT_ENCODING);
    headers.remove(axum::http::header::TRANSFER_ENCODING);

    // Stream body for non-filtered response
    let stream = response.bytes_stream();
    let mut builder = Response::builder().status(status);
    *builder.headers_mut().unwrap() = headers;
    builder.body(Body::from_stream(stream)).map_err(|e| {
        let msg = e.to_string();
        log::error!("Failed to build response: {msg}");
        (StatusCode::INTERNAL_SERVER_ERROR, msg)
    })
}

/// Verifies the response content against a configured endorsement. Fetches the
/// index, locates the endorsement, downloads the blob, and verifies it using
/// `cosign`.
async fn handle_filtered_response(
    response: reqwest::Response,
    filter: &Filter,
    state: &AppState,
) -> Result<Response, (StatusCode, String)> {
    let status = response.status();

    let mut headers = response.headers().clone();

    // Strip headers that might conflict with the new body
    headers.remove(axum::http::header::CONTENT_LENGTH);
    headers.remove(axum::http::header::CONTENT_ENCODING);
    headers.remove(axum::http::header::TRANSFER_ENCODING);

    let body_bytes = response.bytes().await.map_err(|e| {
        let msg = format!("Failed to read response body: {e}");
        log::error!("{msg}");
        (StatusCode::INTERNAL_SERVER_ERROR, msg)
    })?;

    let (subject_digest, subject_path) = cache_subject(&body_bytes)?;

    let mut verification_result =
        Err(VerificationError::EndorsementNotFound(subject_digest.to_string()));

    if let Some(prefix) = &filter.http_index_prefix {
        verification_result = verify_endorsement_from_index(
            &state.client,
            prefix,
            filter,
            &subject_digest,
            &subject_path,
        )
        .await;
    }

    if let Err(e) = verification_result {
        let err_msg = format!("Endorsement verification failed for subject digest: {}.\nError: {}\n\nThe response from the server was not endorsed by the expected identity ({:?}).\n\nTo endorse this content, run the endorsement tool on the saved subject file:\ndoremint blob endorse --file={:?} --repository=<path_to_repo> --valid-for=1d --claims=https://github.com/project-oak/oak/blob/main/docs/tr/claim/94503.md\n",
            subject_digest, e, filter.cosign_identity, subject_path);
        log::error!("{err_msg}");
        return Err((StatusCode::FORBIDDEN, err_msg));
    }

    let mut builder = Response::builder().status(status);
    *builder.headers_mut().unwrap() = headers;
    builder.body(Body::from(body_bytes)).map_err(|e| {
        let msg = e.to_string();
        log::error!("Failed to build response: {msg}");
        (StatusCode::INTERNAL_SERVER_ERROR, msg)
    })
}

/// Caches the subject (response body) to a temporary file and returns its
/// digest and path.
fn cache_subject(body_bytes: &[u8]) -> Result<(Digest, PathBuf), (StatusCode, String)> {
    let digest = compute_canonical_digest(body_bytes);
    let subject_digest = digest.to_string();
    log::info!("Response Subject Digest: {subject_digest}");

    let temp_dir = PathBuf::from("/tmp/mcp_proxy");
    fs::create_dir_all(&temp_dir).map_err(|e| {
        let msg = format!("Failed to create temp dir: {e}");
        log::error!("{msg}");
        (StatusCode::INTERNAL_SERVER_ERROR, msg)
    })?;

    let subject_filename = digest.to_string();
    let subject_path = temp_dir.join(&subject_filename);

    if !subject_path.exists() {
        fs::write(&subject_path, body_bytes).map_err(|e| {
            let msg = format!("Failed to write subject to cache: {e}");
            log::error!("{msg}");
            (StatusCode::INTERNAL_SERVER_ERROR, msg)
        })?;
        log::info!("Subject cached at: {subject_path:?}");
    } else {
        log::info!("Subject already in cache: {subject_path:?}");
    }

    Ok((digest, subject_path))
}

/// Attempts to verify the endorsement for the given subject by consulting the
/// OCI index.
async fn verify_endorsement_from_index(
    client: &reqwest::Client,
    prefix: &str,
    filter: &Filter,
    subject_digest: &Digest,
    subject_path: &Path,
) -> Result<(), VerificationError> {
    let index_url = format!("{}/index.json", prefix.trim_end_matches('/'));
    log::info!("Fetching index from: {index_url}");

    let index = fetch_index(client, &index_url)
        .await
        .map_err(|e| VerificationError::IndexLookupFailed(e.to_string()))?;

    for entry in index.manifests() {
        if let Some(annotations) = entry.annotations() {
            if annotations.get("tr.subject") == Some(&subject_digest.to_string())
                && annotations.get("tr.type") == Some(&"endorsement".to_string())
            {
                let digest_str = entry.digest().to_string();
                log::info!("Found endorsement digest: {digest_str}");

                match verify_candidate_endorsement(
                    client,
                    prefix,
                    filter,
                    &digest_str,
                    subject_path,
                )
                .await
                {
                    Ok(()) => return Ok(()),
                    Err(e) => {
                        log::warn!("Candidate endorsement failed verification: {e}");
                        // Continue checking other candidates
                    }
                }
            }
        }
    }

    Err(VerificationError::EndorsementNotFound(subject_digest.to_string()))
}

/// Downloads, caches, and verifies a specific endorsement blob.
async fn verify_candidate_endorsement(
    client: &reqwest::Client,
    prefix: &str,
    filter: &Filter,
    digest_str: &str,
    subject_path: &Path,
) -> Result<(), VerificationError> {
    let digest = Digest::from_hex(digest_str)
        .map_err(|e| VerificationError::InvalidDigestFormat(e.to_string()))?;

    let blob_url =
        format!("{}/blobs/{}/{}", prefix.trim_end_matches('/'), digest.algo(), digest.to_hex());
    log::info!("Fetching endorsement blob from: {blob_url}");

    let temp_dir = PathBuf::from("/tmp/mcp_proxy");
    let endorsement_path = temp_dir.join(digest_str);

    if !endorsement_path.exists() {
        let resp = client
            .get(&blob_url)
            .send()
            .await
            .map_err(|e| VerificationError::BlobFetchFailed(e.to_string()))?;

        if !resp.status().is_success() {
            return Err(VerificationError::BlobFetchFailed(format!("Status: {}", resp.status())));
        }

        let endorsement_data =
            resp.bytes().await.map_err(|e| VerificationError::BlobFetchFailed(e.to_string()))?;

        let computed_digest = compute_canonical_digest(&endorsement_data);
        if digest == computed_digest {
            log::info!("Endorsement digest verified.");
            fs::write(&endorsement_path, &endorsement_data)
                .map_err(|e| VerificationError::CacheFailed(e.to_string()))?;
            log::info!("Endorsement cached at: {endorsement_path:?}");
        } else {
            log::warn!("Endorsement digest verification failed");
            return Err(VerificationError::DigestMismatch);
        }
    } else {
        log::info!("Endorsement already in cache: {endorsement_path:?}");
    }

    run_cosign_verify_blob(filter, &endorsement_path, subject_path)
}

/// Executes the `cosign` command to verify the endorsement signature over a
/// blob.
fn run_cosign_verify_blob(
    filter: &Filter,
    endorsement_path: &Path,
    subject_path: &Path,
) -> Result<(), VerificationError> {
    log::info!("Calling cosign to verify endorsement...");
    let mut args = vec![
        "verify-blob".to_string(),
        format!("--bundle={}", endorsement_path.to_string_lossy()),
        subject_path.to_string_lossy().to_string(),
    ];

    if let Some(identity) = &filter.cosign_identity {
        args.push(format!("--certificate-identity={identity}"));

        let issuer =
            filter.cosign_oidc_issuer.as_deref().unwrap_or("https://oauth2.sigstore.dev/auth");
        args.push(format!("--certificate-oidc-issuer={issuer}"));
    }
    log::info!("cosign args: {args:?}");

    // Use spawn/output to run cosign
    let output = Command::new("cosign").args(&args).output().map_err(|e| {
        VerificationError::Internal(format!("Failed to execute cosign command: {e}"))
    })?;

    if output.status.success() {
        log::info!("Cosign verification PASSED!");
        log::debug!("Cosign Stdout: {}", String::from_utf8_lossy(&output.stdout));
        Ok(())
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();
        log::warn!("Cosign verification FAILED: {:?}", output.status);
        log::warn!("Cosign Stdout: {}", String::from_utf8_lossy(&output.stdout));
        log::warn!("Cosign Stderr: {}", stderr);
        Err(VerificationError::CosignFailed(stderr))
    }
}

/// Fetches and parses the OCI image index from the given URL.
async fn fetch_index(client: &reqwest::Client, url: &str) -> Result<ImageIndex> {
    let resp = client.get(url).send().await?;
    if !resp.status().is_success() {
        anyhow::bail!("index lookup failed with status: {}", resp.status());
    }
    let body = resp.bytes().await?;
    let index: ImageIndex = serde_json::from_slice(&body)?;
    Ok(index)
}
