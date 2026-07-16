//
// Copyright 2026 The Project Oak Authors
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

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq, Default)]
pub struct RootLayerFeedback {
    pub platform: String,
    pub allow_debug: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hardware_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vmpl: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub amd_product: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub initial_measurement_digest: Option<String>,
}

#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq, Default)]
pub struct KernelLayerFeedback {
    pub kernel_image_digest: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub init_ram_fs_digest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub memory_map_digest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kernel_cmd_line: Option<String>,
}

#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq, Default)]
pub struct WorkloadLayerFeedback {
    pub workload_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub container_image_digest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub container_bundle_digest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub workload_config_digest: Option<String>,
}

#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq, Default)]
pub struct VerifiedSessionKeys {
    pub session_binding_public_key: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub encryption_public_key: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signing_public_key: Option<String>,
}

/// Rich, self-contained attestation feedback payload serialized into
/// `X-Oak-Attestation`.
#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq, Default)]
pub struct OakAttestationFeedback {
    pub status: String,
    pub handshake_handle: String,
    pub verification_time: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub matched_endorsement_digest: Option<String>,
    pub root_layer: RootLayerFeedback,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kernel_layer: Option<KernelLayerFeedback>,
    pub workload_layer: WorkloadLayerFeedback,
    pub session_keys: VerifiedSessionKeys,
    #[serde(skip_serializing_if = "BTreeMap::is_empty", default)]
    pub custom_artifacts: BTreeMap<String, String>,
}

#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ProxyFailureCode {
    AttestationVerificationFailed,
    UpstreamConnectionFailed,
    HandshakeTimeout,
    ProtocolError,
}

#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq, Default)]
pub struct NetworkErrorDetails {
    pub peer_address: String,
    pub io_error_kind: String,
}

#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq, Default)]
pub struct EndorsementMismatchDetails {
    pub expected_predicate: String,
    pub received_predicate: String,
}

#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq, Default)]
pub struct ProxyFailureDetails {
    pub failure_reason: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub network_error: Option<NetworkErrorDetails>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub expected_digests: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub received_digest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub endorsement_mismatch: Option<EndorsementMismatchDetails>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rejected_due_to_debug_mode: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hardware_root_error: Option<String>,
}

/// Complete HTTP 502 Bad Gateway JSON body emitted upon failure under `--http`.
#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq)]
pub struct OakProxyFailureResponse {
    pub error_code: ProxyFailureCode,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub handshake_handle: Option<String>,
    pub details: ProxyFailureDetails,
    pub timestamp: String,
}

/// Inspects an `anyhow::Error` string representation and categorizes it into a
/// `ProxyFailureCode`.
pub fn categorize_proxy_error(err: &anyhow::Error) -> ProxyFailureCode {
    let msg = format!("{:#}", err).to_lowercase();
    if msg.contains("attestation")
        || msg.contains("endorsement")
        || msg.contains("policy")
        || msg.contains("digest")
        || msg.contains("verifier")
        || msg.contains("evidence")
    {
        ProxyFailureCode::AttestationVerificationFailed
    } else if msg.contains("timeout") || msg.contains("timed out") {
        ProxyFailureCode::HandshakeTimeout
    } else if msg.contains("connect")
        || msg.contains("connection")
        || msg.contains("refused")
        || msg.contains("no route")
    {
        ProxyFailureCode::UpstreamConnectionFailed
    } else {
        ProxyFailureCode::ProtocolError
    }
}

/// Splices the `X-Oak-Attestation` header right before the `\r\n\r\n` boundary
/// in `buf`.
///
/// Uses pure `core::slice` window searching with zero HTTP parser dependencies.
/// Returns `Some(vec)` containing the spliced frame if the HTTP header boundary
/// `\r\n\r\n` is found; otherwise returns `None`.
/// Checks whether a buffer starts with an HTTP method or status line.
pub fn is_http_start(buf: &[u8]) -> bool {
    buf.starts_with(b"HTTP/")
        || buf.starts_with(b"GET ")
        || buf.starts_with(b"POST ")
        || buf.starts_with(b"PUT ")
        || buf.starts_with(b"DELETE ")
        || buf.starts_with(b"HEAD ")
        || buf.starts_with(b"OPTIONS ")
        || buf.starts_with(b"PATCH ")
}

/// Splices the `X-Oak-Attestation` header right before the `\r\n\r\n` boundary
/// in `buf`.
///
/// Uses pure `core::slice` window searching with zero HTTP parser dependencies.
/// Strips any pre-existing `X-Oak-Attestation` headers (case-insensitive)
/// before appending the authenticated attestation header.
/// Returns `Some(vec)` containing the spliced frame if the HTTP header boundary
/// `\r\n\r\n` is found; otherwise returns `None`.
pub fn splice_attestation_header(buf: &[u8], feedback_json_base64: &str) -> Option<Vec<u8>> {
    if !is_http_start(buf) {
        return None;
    }
    let pos = buf.windows(4).position(|w| w == b"\r\n\r\n")?;

    // Strip any pre-existing X-Oak-Attestation header lines from the HTTP headers
    // slice before splicing.
    let mut cleaned_headers = Vec::with_capacity(pos);
    let mut i = 0;
    while i < pos {
        if pos - i >= 2 && &buf[i..i + 2] == b"\r\n" {
            let line_start = i + 2;
            let line_end = buf[line_start..pos]
                .windows(2)
                .position(|w| w == b"\r\n")
                .map(|p| line_start + p)
                .unwrap_or(pos);
            let line = &buf[line_start..line_end];
            if line.len() >= 18 && line[..18].eq_ignore_ascii_case(b"X-Oak-Attestation:") {
                i = line_end;
                continue;
            }
        }
        cleaned_headers.push(buf[i]);
        i += 1;
    }

    let header_line = format!("\r\nX-Oak-Attestation: {}", feedback_json_base64);
    let header_bytes = header_line.as_bytes();

    let mut spliced =
        Vec::with_capacity(cleaned_headers.len() + header_bytes.len() + (buf.len() - pos));
    spliced.extend_from_slice(&cleaned_headers);
    spliced.extend_from_slice(header_bytes);
    spliced.extend_from_slice(&buf[pos..]);
    Some(spliced)
}

/// Formats a complete `HTTP/1.1 502 Bad Gateway` response containing
/// `failure_response` serialized as JSON.
pub fn format_502_error_response(failure_response: &OakProxyFailureResponse) -> Vec<u8> {
    let body_json = serde_json::to_string_pretty(failure_response)
        .unwrap_or_else(|_| "{\"error_code\":\"protocol_error\"}".to_string());
    let response = format!(
        "HTTP/1.1 502 Bad Gateway\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
        body_json.len(),
        body_json
    );
    response.into_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_splice_attestation_header() {
        let raw_http = b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\nHello World";
        let feedback_b64 = "eyJzdGF0dXMiOiJ2ZXJpZmllZCJ9";

        let spliced = splice_attestation_header(raw_http, feedback_b64).expect("splicing failed");
        let spliced_str = std::str::from_utf8(&spliced).expect("invalid utf8");

        assert!(spliced_str.contains("X-Oak-Attestation: eyJzdGF0dXMiOiJ2ZXJpZmllZCJ9"));
        assert!(spliced_str.ends_with("\r\n\r\nHello World"));
        assert!(
            spliced_str
                .starts_with("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nX-Oak-Attestation:")
        );
    }

    #[test]
    fn test_splice_attestation_header_no_boundary() {
        let incomplete = b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n";
        assert!(splice_attestation_header(incomplete, "abc").is_none());
    }

    #[test]
    fn test_splice_attestation_header_request_methods() {
        let raw_post = b"POST /api/v1/submit HTTP/1.1\r\nHost: localhost\r\n\r\n{\"foo\":\"bar\"}";
        let feedback_b64 = "eyJzdGF0dXMiOiJ2ZXJpZmllZCJ9";
        let spliced = splice_attestation_header(raw_post, feedback_b64).expect("splicing failed");
        let spliced_str = std::str::from_utf8(&spliced).expect("invalid utf8");

        assert!(spliced_str.contains("X-Oak-Attestation: eyJzdGF0dXMiOiJ2ZXJpZmllZCJ9"));
        assert!(
            spliced_str.starts_with(
                "POST /api/v1/submit HTTP/1.1\r\nHost: localhost\r\nX-Oak-Attestation:"
            )
        );
        assert!(spliced_str.ends_with("\r\n\r\n{\"foo\":\"bar\"}"));
    }

    #[test]
    fn test_splice_attestation_header_strips_existing() {
        let raw_http = b"HTTP/1.1 200 OK\r\nX-Oak-Attestation: bogus_old_value\r\nContent-Type: text/plain\r\nX-oak-attestation: another_bogus\r\n\r\nHello World";
        let feedback_b64 = "eyJzdGF0dXMiOiJ2ZXJpZmllZCJ9";

        let spliced = splice_attestation_header(raw_http, feedback_b64).expect("splicing failed");
        let spliced_str = std::str::from_utf8(&spliced).expect("invalid utf8");

        assert!(spliced_str.contains("X-Oak-Attestation: eyJzdGF0dXMiOiJ2ZXJpZmllZCJ9"));
        assert!(!spliced_str.contains("bogus_old_value"));
        assert!(!spliced_str.contains("another_bogus"));
        assert!(spliced_str.ends_with("\r\n\r\nHello World"));
    }

    #[test]
    fn test_splice_attestation_header_non_http_rejected() {
        let binary_payload = b"\x00\x01\x02\x03\r\n\r\nsome binary data";
        assert!(splice_attestation_header(binary_payload, "abc").is_none());
    }

    #[test]
    fn test_format_502_error_response() {
        let failure = OakProxyFailureResponse {
            error_code: ProxyFailureCode::AttestationVerificationFailed,
            handshake_handle: Some("8f3c2b1e".to_string()),
            details: ProxyFailureDetails {
                failure_reason: "digest mismatch".to_string(),
                ..Default::default()
            },
            timestamp: "2026-07-16T12:00:00Z".to_string(),
        };

        let response_bytes = format_502_error_response(&failure);
        let response_str = std::str::from_utf8(&response_bytes).expect("invalid utf8");

        assert!(response_str.starts_with("HTTP/1.1 502 Bad Gateway\r\n"));
        assert!(response_str.contains("Content-Type: application/json"));
        assert!(response_str.contains("\"error_code\": \"attestation_verification_failed\""));
        assert!(response_str.contains("\"digest mismatch\""));
    }

    #[test]
    fn test_categorize_proxy_error() {
        let attestation_err = anyhow::anyhow!("Attestation verification failed: policy mismatch");
        assert_eq!(
            categorize_proxy_error(&attestation_err),
            ProxyFailureCode::AttestationVerificationFailed
        );

        let timeout_err = anyhow::anyhow!("Handshake timed out after 10s");
        assert_eq!(categorize_proxy_error(&timeout_err), ProxyFailureCode::HandshakeTimeout);

        let connect_err = anyhow::anyhow!("Connection refused (os error 111)");
        assert_eq!(
            categorize_proxy_error(&connect_err),
            ProxyFailureCode::UpstreamConnectionFailed
        );

        let proto_err = anyhow::anyhow!("Invalid noise message format");
        assert_eq!(categorize_proxy_error(&proto_err), ProxyFailureCode::ProtocolError);
    }
}
