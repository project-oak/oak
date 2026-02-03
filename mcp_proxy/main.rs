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

use std::{fs, path::PathBuf};

use anyhow::{Context, Result};
use axum::{
    Router,
    body::Body,
    extract::{Request, State},
    http::StatusCode,
    response::Response,
    routing::any,
};
use clap::Parser;
use config::{Config, Filter};
use digest::{Digest, compute_canonical_digest};
use oak_proto_rust::oak::HexDigest;
use thiserror::Error;
use tokio::net::TcpListener;
use trex_client::{
    EndorsementVerifier,
    http::{HttpBlobFetcher, HttpEndorsementIndex, fetch_index},
};

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

/// Claim associated with a "good" MCP tool list (including tool names and
/// descriptions).
const MCP_TOOL_LIST_CLAIM_TYPE: &str =
    "https://github.com/project-oak/oak/blob/main/docs/tr/claim/94503.md";

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
/// caches responses, and optionally verifies them based on configuration
/// filters.
async fn handle_request(
    State(state): State<AppState>,
    req: Request,
) -> Result<Response, (StatusCode, String)> {
    let (parts, body) = req.into_parts();
    let path = parts.uri.path().to_string();
    let method_str = parts.method.to_string();

    log::info!("================================================================");
    log::info!("⇒ Request: {} {}", method_str, path);

    // Read all the request body to extract method for filtering.
    let body_bytes = axum::body::to_bytes(body, usize::MAX).await.map_err(|e| {
        let msg = format!("Failed to read HTTP request body: {e}");
        log::error!("{msg}");
        (StatusCode::INTERNAL_SERVER_ERROR, msg)
    })?;

    let mut json_rpc_method = None;
    if !body_bytes.is_empty() {
        if let Ok(json_req) = serde_json::from_slice::<serde_json::Value>(&body_bytes) {
            log::debug!("Parsed HTTP request body as JSON: {json_req:?}");
            if let Some(m) = json_req.get("method").and_then(|v| v.as_str()) {
                json_rpc_method = Some(m.to_string());
                log::info!("   JSON-RPC Method: {m}");
            }
        } else {
            log::warn!("   HTTP Request body not JSON or malformed");
        }
    }

    let path_query = parts.uri.path_and_query().map(|pq| pq.as_str()).unwrap_or(parts.uri.path());
    let target_base = state.config.target_mcp_server_url.trim_end_matches('/');
    let target_uri_str = format!("{}{}", target_base, path_query);
    log::info!("   Forwarding to: {target_uri_str}");

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

    let status = response.status();
    log::info!("⇐ Response Status: {}", status);

    let mut headers = response.headers().clone();
    // Strip headers that might conflict with the new body/stream
    headers.remove(axum::http::header::CONTENT_LENGTH);
    headers.remove(axum::http::header::CONTENT_ENCODING);
    headers.remove(axum::http::header::TRANSFER_ENCODING);

    // Read response body (ALWAYS, to cache it)
    let resp_body_bytes = response.bytes().await.map_err(|e| {
        let msg = format!("Failed to read response body: {e}");
        log::error!("{msg}");
        (StatusCode::INTERNAL_SERVER_ERROR, msg)
    })?;

    // Cache the response
    let (digest, path) = cache_subject(&resp_body_bytes)?;
    log::info!("   Digest: {}", digest);
    log::info!("   Cached: {:?}", path);

    // Endorsement Verification
    if let Some(method) = &json_rpc_method {
        let matched_filter = state.config.filters.iter().find(|f| f.method == *method);
        if let Some(filter) = matched_filter {
            if filter.cosign_identity.is_some() {
                log::info!("   Verifying endorsement for method: {}", method);
                if let Err(e) = verify_endorsement(filter, &digest, &path).await {
                    log::info!("   ❌ Verification failed");
                    log::info!("================================================================");
                    return Err(e);
                }
                log::info!("   ✅ Verification successful");
            }
        } else {
            log::info!("   ✅ Allowed (no verification required)");
        }
    }

    log::info!("================================================================");
    let mut builder = Response::builder().status(status);
    *builder.headers_mut().unwrap() = headers;
    builder.body(Body::from(resp_body_bytes)).map_err(|e| {
        let msg = e.to_string();
        log::error!("Failed to build response: {msg}");
        (StatusCode::INTERNAL_SERVER_ERROR, msg)
    })
}

/// Verifies the response content against a configured endorsement. Fetches the
/// index, locates the endorsement, downloads the blob, and verifies it using
/// `cosign`.
async fn verify_endorsement(
    filter: &Filter,
    subject_digest_local: &Digest,
    subject_path: &PathBuf,
) -> Result<(), (StatusCode, String)> {
    let subject_digest =
        HexDigest { sha2_256: subject_digest_local.to_hex(), ..Default::default() };

    if let Some(index_url) = &filter.endorsement_index_url {
        log::info!("   Loading endorsement index from {index_url}");
        let index = fetch_index(index_url).await.map_err(|e| {
            let msg = format!("Failed to fetch endorsement index: {e}");
            log::error!("{msg}");
            (StatusCode::INTERNAL_SERVER_ERROR, msg)
        })?;

        // This currently assumes that there's a single OCI CAS client in the index. In
        // the future, we'll need to handle multiple CAS clients (e.g. OCI, Git-style,
        // etc.) and allow the user to select which one to use.
        let cas_client = index.cas_clients.first().expect("no CAS clients found in the index");

        let fetcher = Box::new(HttpBlobFetcher::new(cas_client.clone()));
        let verifier = EndorsementVerifier::new(
            Box::new(HttpEndorsementIndex::new(Box::new(move || index.clone()))),
            fetcher,
        );

        let now = oak_time_std::instant::now();
        let required_claims = vec![MCP_TOOL_LIST_CLAIM_TYPE.to_string()];

        let identity = filter.cosign_identity.as_deref().unwrap_or_default();
        let issuer =
            filter.cosign_oidc_issuer.as_deref().unwrap_or("https://oauth2.sigstore.dev/auth");

        let result =
            verifier.verify(&subject_digest, now, &required_claims, identity, issuer).await;

        if let Err(e) = result {
            let err_msg = format!(
                "Endorsement verification failed for subject digest: {subject_digest_local}.\nError: {e:?}\n\nThe response from the server was not endorsed by the expected identity ({:?}).\n\nTo endorse this content, run the endorsement tool on the saved subject file:\ndoremint blob endorse --file={subject_path:?} --repository=<path_to_repo> --valid-for=1d --claims=\"{MCP_TOOL_LIST_CLAIM_TYPE}\"\n",
                filter.cosign_identity
            );
            log::error!("{err_msg}");
            return Err((StatusCode::FORBIDDEN, err_msg));
        }
    }
    Ok(())
}

/// Caches the subject (response body) to a temporary file and returns its
/// digest and path.
fn cache_subject(body_bytes: &[u8]) -> Result<(Digest, PathBuf), (StatusCode, String)> {
    let digest = compute_canonical_digest(body_bytes);

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
    }

    Ok((digest, subject_path))
}
