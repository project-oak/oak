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
    io::{BufRead, BufReader, Read, Write},
    os::unix::net::UnixStream,
};

#[derive(thiserror::Error, Debug)]
pub enum AttestationRequestError {
    #[error("{0}: {1}")]
    InternalError(String, #[source] Box<dyn std::error::Error + Send + Sync>),

    #[error("{0}")]
    OtherError(String),
}

use AttestationRequestError::{InternalError, OtherError};

/// Reads the Confidential Space attestation token made available to a container
/// image.
///
/// The token can be used to verify the Confidential Space setup by the
/// container image. It should not be used for attestation of a specific user
/// session since it does not contain information about the user session (i.e. a
/// nonce).
pub fn read_confidential_space_attestation() -> Result<String, AttestationRequestError> {
    // The path to the Confidential Space attestation token file, as documented in
    // Google Cloud documentation[^1].
    //
    // [^1]: https://cloud.google.com/confidential-computing/confidential-space/docs/create-customize-workloads#expired-tokens
    const CONFIDENTIAL_SPACE_ATTESTATION_TOKEN_PATH: &str =
        "/run/container_launcher/attestation_verifier_claims_token";

    let token_str = fs::read_to_string(CONFIDENTIAL_SPACE_ATTESTATION_TOKEN_PATH).map_err(|e| {
        InternalError("Failed to read Confidential Space attestation token".to_string(), e.into())
    })?;

    Ok(token_str)
}

/// Requests a Confidential Space attestation token from the Confidential Space
/// TEE.
///
/// `nonce` must be between 8 and 88 bytes long (inclusive)[^1].
///
/// The token can be used to prove to clients of a container about the claims
/// that are upheld by the Confidential Space TEE. For more information about
/// the supported claims and the format see Google Cloud documentation[^1].
///
/// In particular, the requested token will always be of type "PKI" and will be
/// signed with the Confidential Space root certificate specified in the
/// root_ca_uri field at the PKI token endpoint[^2].
///
/// In order to request a token, this function has to open a Unix domain socket
/// and make an HTTP request through it. The Unix domain socket location, the
/// resource path and the request and response format is specified in the GCP
/// documentation[^3].
///
/// [^1]: https://cloud.google.com/confidential-computing/confidential-space/docs/reference/token-claims
/// [^2]: https://confidentialcomputing.googleapis.com/.well-known/attestation-pki-root.
/// [^3]: https://cloud.google.com/confidential-computing/confidential-space/docs/connect-external-resources#retrieve_attestation_tokens
pub fn request_attestation_token(
    audience: &str,
    nonce: &str,
) -> Result<String, AttestationRequestError> {
    const TEE_SERVER_SOCKET_PATH: &str = "/run/container_launcher/teeserver.sock";

    // Connect to the Unix domain socket.
    let stream = UnixStream::connect(TEE_SERVER_SOCKET_PATH)
        .map_err(|e| InternalError("Failed to connect to TEE server".to_string(), e.into()))?;

    // Create a JSON request body. The token type is set to "PKI" to indicate that
    // the token is a public key infrastructure token.
    let request_body = serde_json::json!({
        "token_type": "PKI",
        "audience": audience,
        "nonces": vec![nonce],
    })
    .to_string();

    // Use the http crate to build the request.
    let request = http::Request::builder()
        .method("POST")
        .uri("/v1/token")
        .header("Host", "localhost")
        .header("Content-Type", "application/json")
        .header("Content-Length", request_body.len())
        .body(request_body)
        .expect("Failed to build HTTP request");

    let response = http_request(&stream, request)?;

    Ok(response.into_body())
}

// This is a helper function to make HTTP requests to the Confidential Space TEE
// through a Unix domain socket. At the moment it is quite brittle and could
// easily break if the TEE server changes the way it responds. We should
// consider implementing it using a more robust client library but unfortunately
// support for Unix domain sockets is pretty sparse in Rust HTTP clients.
fn http_request(
    mut stream: &UnixStream,
    request: http::Request<String>,
) -> Result<http::Response<String>, AttestationRequestError> {
    // Write the HTTP request to the stream.
    write!(&mut stream, "{} {} {:?}\r\n", request.method(), request.uri(), request.version())
        .map_err(|e| InternalError("Failed to write HTTP preamble".to_string(), e.into()))?;
    for (name, value) in request.headers() {
        let value = value
            .to_str()
            .map_err(|e| InternalError("Failed to convert HTTP header".to_string(), e.into()))?;
        write!(&mut stream, "{}: {}\r\n", name, value)
            .map_err(|e| InternalError("Failed to write HTTP header".to_string(), e.into()))?;
    }
    write!(&mut stream, "\r\n")
        .map_err(|e| InternalError("Failed to write HTTP request".to_string(), e.into()))?;

    write!(&mut stream, "{}", request.body())
        .map_err(|e| InternalError("Failed to write HTTP request body".to_string(), e.into()))?;
    stream.flush().map_err(|e| InternalError("Failed to flush stream".to_string(), e.into()))?;

    // Read the response from the stream.
    let mut reader = BufReader::new(stream);

    // Parse status line.
    let mut status_line = String::new();
    reader.read_line(&mut status_line).map_err(|e| {
        InternalError("Failed to read HTTP response status line".to_string(), e.into())
    })?;
    let mut parts = status_line.split_whitespace();
    let version = match parts.next() {
        Some("HTTP/1.1") => http::Version::HTTP_11,
        Some(version) => {
            return Err(OtherError(format!("Unsupported or malformed HTTP version: {}", version)));
        }
        None => return Err(OtherError("Malformed HTTP response: missing version".to_string())),
    };
    let status = match parts.next() {
        Some(code) => code.parse::<http::StatusCode>().map_err(|e| {
            InternalError("Malformed HTTP response: malformed status code".to_string(), e.into())
        })?,
        _ => return Err(OtherError("Malformed HTTP response: missing status code".to_string())),
    };

    let mut builder = http::Response::builder().status(status).version(version);

    let mut content_length: Option<usize> = None;
    let mut chunked = false;
    loop {
        let mut header_line = String::new();
        reader.read_line(&mut header_line).map_err(|e| {
            InternalError("Failed to read HTTP response header line".to_string(), e.into())
        })?;
        let header_line = header_line.trim();
        if header_line.is_empty() {
            break; // End of headers
        }
        let (name, value) = header_line
            .split_once(':')
            .ok_or(OtherError(format!("Malformed HTTP header: {}", header_line)))?;
        let (name, value) = (name.trim(), value.trim());
        match name {
            "Content-Length" => {
                let parsed = value
                    .parse::<usize>()
                    .map_err(|e| InternalError("Malformed Content-Length".to_string(), e.into()))?;
                content_length = Some(parsed);
            }
            "Transfer-Encoding" => chunked = value == "chunked",
            _ => (), // Ignore other headers, they are not important.
        }
        builder = builder.header(name, value);
    }

    let body = match content_length {
        Some(len) => {
            let mut body = vec![0; len];
            reader.read_exact(&mut body).map_err(|e| {
                InternalError("Failed to read HTTP response body".to_string(), e.into())
            })?;
            body
        }
        None => {
            let mut body = Vec::new();
            if chunked {
                loop {
                    // Read the line containing the chunk size in hex.
                    let mut size_line = String::new();
                    reader.read_line(&mut size_line).map_err(|e| {
                        InternalError("Failed to read chunk size".to_string(), e.into())
                    })?;
                    let chunk_size = usize::from_str_radix(size_line.trim(), 16)
                        .map_err(|e| InternalError("Malformed chunk size".to_string(), e.into()))?;

                    if chunk_size == 0 {
                        // This is the last chunk. Consume the trailing CRLF and break.
                        reader.read_line(&mut String::new()).map_err(|e| {
                            InternalError("Failed to read final CRLF".to_string(), e.into())
                        })?;
                        break;
                    }

                    // Read the chunk data.
                    let mut chunk_data = vec![0; chunk_size];
                    reader.read_exact(&mut chunk_data).map_err(|e| {
                        InternalError("Failed to read chunk data".to_string(), e.into())
                    })?;
                    body.extend_from_slice(&chunk_data);

                    // Consume the CRLF after the chunk data.
                    reader.read_line(&mut String::new()).map_err(|e| {
                        InternalError("Failed to read CRLF after chunk".to_string(), e.into())
                    })?;
                }
            } else {
                reader.read_to_end(&mut body).map_err(|e| {
                    InternalError("Failed to read HTTP response body".to_string(), e.into())
                })?;
            }
            body
        }
    };

    let body_str = String::from_utf8(body).map_err(|e| {
        InternalError("Failed to convert HTTP response body to string".to_string(), e.into())
    })?;

    builder
        .body(body_str)
        .map_err(|e| InternalError("Failed to extract HTTP response body".to_string(), e.into()))
}
