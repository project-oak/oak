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

//! # Cleanroom SDK
//!
//! Ergonomic wrappers for writing WebAssembly modules that run inside
//! the [cleanroom](../README.md) sandboxed runner.
//!
//! Modules use **standard Rust I/O** for stdin/stdout/stderr and
//! **standard HTTP crates** (e.g. `waki`) for network requests.
//! IFC enforcement is handled automatically by the runtime.
//!
//! This SDK provides wrappers for:
//!
//! - **IFC metadata**: [`get_label`], [`read_cell`]
//! - **Proxied filesystem**: [`read_file`], [`write_file`], [`delete_file`],
//!   [`list_directory`]
//!
//! ## Usage
//!
//! ```ignore
//! fn main() {
//!     let secret = cleanroom_sdk::read_cell("api_key")
//!         .expect("missing cell");
//!     let redacted = format!("{}****\n", &secret[..4]);
//!     print!("{redacted}");
//! }
//! ```

// Generate the WIT bindings once, here in the SDK crate.
wit_bindgen::generate!({
    path: "../../cleanroom/wit",
    world: "runner",
});

/// Dual-component IFC label.
///
/// Secrecy lists the principals whose authorization is needed to
/// release the data.  Integrity lists the principals who vouch for
/// the data's correctness.
pub struct Label {
    pub secrecy: Vec<String>,
    pub integrity: Vec<String>,
}

/// Returns the current (immutable) computation label.
///
/// The label is fixed at module spawn time and does not change
/// during execution.
pub fn get_label() -> Label {
    let wit_label = oak::cleanroom::ifc::get_label();
    Label { secrecy: wit_label.secrecy, integrity: wit_label.integrity }
}

/// Reads a named cell from the host cell store.
///
/// The cell's label must flow to the computation's label for the
/// read to succeed.  The module's full privilege is applied
/// automatically by the runtime.
///
/// Returns `None` if the cell is not defined or if the flow check
/// fails.
pub fn read_cell(name: &str) -> Option<String> {
    oak::cleanroom::ifc::read_cell(name)
}

/// Reads a file via the filesystem proxy.
///
/// The file path is relative to the caller's working directory.
/// The file content is fetched from the client's sandbox over the
/// Unix socket.
pub fn read_file(path: &str) -> std::result::Result<Vec<u8>, String> {
    oak::cleanroom::fs::read_file(path)
}

/// Writes a file via the filesystem proxy.
///
/// The file path is relative to the caller's working directory.
/// Parent directories are created automatically by the client.
pub fn write_file(path: &str, data: &[u8]) -> std::result::Result<(), String> {
    oak::cleanroom::fs::write_file(path, data)
}

/// Deletes a file via the filesystem proxy.
pub fn delete_file(path: &str) -> std::result::Result<(), String> {
    oak::cleanroom::fs::delete_file(path)
}

/// Lists directory contents via the filesystem proxy.
///
/// Returns a list of file/directory names in the given path.
pub fn list_directory(path: &str) -> std::result::Result<Vec<String>, String> {
    oak::cleanroom::fs::list_directory(path)
}

/// An HTTP response returned by [`http_request`].
pub struct HttpResponse {
    /// HTTP status code (e.g. 200, 404).
    pub status: u16,
    /// Response headers as key-value pairs.
    pub headers: Vec<(String, String)>,
    /// Response body bytes.
    pub body: Vec<u8>,
}

/// Makes an HTTP request.
///
/// IFC enforcement is automatic: the runtime checks that the
/// computation label flows to public (with the module's full
/// privilege) before sending.
pub fn http_request(
    method: &str,
    url: &str,
    headers: &[(&str, &str)],
    body: Option<&[u8]>,
) -> Result<HttpResponse, String> {
    let headers_owned: Vec<(String, String)> =
        headers.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect();
    let body_owned = body.map(|b| b.to_vec());

    let request = oak::cleanroom::http::HttpRequest {
        method: method.to_string(),
        url: url.to_string(),
        headers: headers_owned,
        body: body_owned,
    };

    let resp = oak::cleanroom::http::send_request(&request)?;

    Ok(HttpResponse { status: resp.status, headers: resp.headers, body: resp.body })
}

/// Convenience: HTTP GET.
pub fn http_get(url: &str, headers: &[(&str, &str)]) -> Result<HttpResponse, String> {
    http_request("GET", url, headers, None)
}

/// Convenience: HTTP POST.
pub fn http_post(url: &str, headers: &[(&str, &str)], body: &[u8]) -> Result<HttpResponse, String> {
    http_request("POST", url, headers, Some(body))
}
