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

//! RPC protocol for communication between the cleanroom thin client
//! (inside the container) and the cleanroom server (on the host).
//!
//! Messages are serialized with [`bincode`] and framed with a 4-byte
//! little-endian length prefix over a Unix domain socket.
//!
//! # Wire format
//!
//! ```text
//! [length: u32 LE] [bincode payload: length bytes]
//! ```

use std::io::{Read, Write};

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};

use crate::ifc::Label;

/// A message from the client to the server.
#[derive(Debug, Serialize, Deserialize)]
pub enum ClientToServer {
    /// Run a Wasm module with the given stdin bytes.
    Run {
        /// Content digest of the module (e.g. `sha256:e3b0c44...`).
        digest: String,
        /// Bytes to feed as stdin to the module.
        stdin: Vec<u8>,
        /// Initial label for the computation.
        ///
        /// The **integrity** component identifies the caller: the
        /// principals who vouch for the stdin data.  The server
        /// derives the output channel label from this set.
        ///
        /// The **secrecy** component specifies what secret data the
        /// module may access.  The module must be authorized (via
        /// `speaks_for`) for every secrecy principal beyond the
        /// caller's own identity.
        ///
        /// Default is the public label (anonymous, no secret access).
        #[serde(default)]
        label: Label,
        /// Command-line arguments forwarded to the module.
        ///
        /// These are provided to the module via WASI `args` and can
        /// be read with `std::env::args()` or parsed with `clap`.
        #[serde(default)]
        args: Vec<String>,
    },
    /// List all modules registered in the manifest.
    ListModules,
    /// Query the policy for a specific module.
    QueryPolicy {
        /// Content digest of the module.
        digest: String,
    },
    /// Custom FsReadFile Result (None if the file does not exist).
    FsReadFileResult { data: Option<Vec<u8>> },
    /// Custom FsWriteFile Result
    FsWriteFileResult { success: bool },
    /// Custom FsDeleteFile Result
    FsDeleteFileResult { success: bool },
    /// Custom FsListDirectory Result
    FsListDirectoryResult { entries: Vec<String> },
}

/// The status of a module execution.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RunStatus {
    /// Module executed successfully.
    Ok,
    /// Module execution was trapped (Wasm trap or IFC violation).
    Trapped,
    /// Module was denied by the policy (unknown digest, etc.).
    PolicyDenied,
}

/// A message from the server to the client.
#[derive(Debug, Serialize, Deserialize)]
pub enum ServerToClient {
    /// Result of running a module.
    RunResult {
        /// Execution status.
        status: RunStatus,
        /// Module's stdout output.
        stdout: Vec<u8>,
        /// Module's stderr output.
        stderr: Vec<u8>,
    },
    /// List of registered modules.
    ModuleList {
        /// Modules with their names and digests.
        modules: Vec<ModuleInfo>,
    },
    /// Policy information for a module.
    PolicyInfo {
        /// Categories the module is privileged to declassify.
        can_declassify: Vec<String>,
    },
    /// An error occurred.
    Error {
        /// Human-readable error message.
        message: String,
    },
    /// Custom FsReadFile Request
    FsReadFile { path: String },
    /// Custom FsWriteFile Request
    FsWriteFile { path: String, data: Vec<u8> },
    /// Custom FsDeleteFile Request
    FsDeleteFile { path: String },
    /// Custom FsListDirectory Request
    FsListDirectory { path: String },
}

/// Summary information about a registered module.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleInfo {
    /// Human-readable name.
    pub name: String,
    /// Content digest.
    pub digest: String,
}

/// Writes a length-prefixed bincode message to a stream.
pub fn write_message<W: Write, T: Serialize>(writer: &mut W, msg: &T) -> Result<()> {
    let size = bincode::serialized_size(msg).context("calculating message size")?;
    let len = u32::try_from(size).context("message too large")?;
    writer.write_all(&len.to_le_bytes()).context("writing message length")?;
    bincode::serialize_into(&mut *writer, msg).context("serializing message payload")?;
    writer.flush().context("flushing message")?;
    Ok(())
}

/// Reads a length-prefixed bincode message from a stream.
pub fn read_message<R: Read, T: for<'de> Deserialize<'de>>(reader: &mut R) -> Result<T> {
    let mut len_buf = [0u8; 4];
    reader.read_exact(&mut len_buf).context("reading message length")?;
    let len = u32::from_le_bytes(len_buf) as usize;

    let mut limited_reader = reader.take(len as u64);
    let msg = bincode::deserialize_from(&mut limited_reader).context("deserializing message")?;

    // Discard any remainder if bincode stopped early.
    std::io::copy(&mut limited_reader, &mut std::io::sink())
        .context("discarding remainder of message")?;

    Ok(msg)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ifc::Principal;

    #[test]
    fn roundtrip_run_request() {
        let req = ClientToServer::Run {
            digest: "sha256:abc123".to_string(),
            stdin: b"hello world".to_vec(),
            label: Label::new(
                vec![Principal::new("secret_category"), Principal::new("tzn")],
                vec![Principal::new("tzn")],
            ),
            args: vec!["--lockfile=Cargo.lock".to_string()],
        };

        let mut buf = Vec::new();
        write_message(&mut buf, &req).unwrap();

        let mut cursor = std::io::Cursor::new(buf);
        let decoded: ClientToServer = read_message(&mut cursor).unwrap();

        match decoded {
            ClientToServer::Run { digest, stdin, label, args } => {
                assert_eq!(digest, "sha256:abc123");
                assert_eq!(stdin, b"hello world");
                assert_eq!(label.secrecy_names(), vec!["secret_category", "tzn"]);
                assert_eq!(label.integrity_names(), vec!["tzn"]);
                assert_eq!(args, vec!["--lockfile=Cargo.lock"]);
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn roundtrip_run_result() {
        let resp = ServerToClient::RunResult {
            status: RunStatus::Ok,
            stdout: b"HELLO WORLD".to_vec(),
            stderr: Vec::new(),
        };

        let mut buf = Vec::new();
        write_message(&mut buf, &resp).unwrap();

        let mut cursor = std::io::Cursor::new(buf);
        let decoded: ServerToClient = read_message(&mut cursor).unwrap();

        match decoded {
            ServerToClient::RunResult { status, stdout, stderr } => {
                assert_eq!(status, RunStatus::Ok);
                assert_eq!(stdout, b"HELLO WORLD");
                assert!(stderr.is_empty());
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn roundtrip_list_modules() {
        let req = ClientToServer::ListModules;

        let mut buf = Vec::new();
        write_message(&mut buf, &req).unwrap();

        let mut cursor = std::io::Cursor::new(buf);
        let decoded: ClientToServer = read_message(&mut cursor).unwrap();

        assert!(matches!(decoded, ClientToServer::ListModules));
    }

    #[test]
    fn roundtrip_error() {
        let resp = ServerToClient::Error { message: "something went wrong".to_string() };

        let mut buf = Vec::new();
        write_message(&mut buf, &resp).unwrap();

        let mut cursor = std::io::Cursor::new(buf);
        let decoded: ServerToClient = read_message(&mut cursor).unwrap();

        match decoded {
            ServerToClient::Error { message } => assert_eq!(message, "something went wrong"),
            _ => panic!("wrong variant"),
        }
    }
}
