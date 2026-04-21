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

//! Wasmtime host implementation for the `oak:cleanroom` interfaces.
//!
//! I/O flow:
//!
//! - **Stdin/stdout/stderr** are standard WASI pipes.  IFC enforcement happens
//!   at module boundary — the server checks whether the computation label flows
//!   to the channel label (with the module's full privilege applied
//!   automatically) before releasing output to the caller.
//!
//! - **HTTP** is standard WASI HTTP.  The host overrides the outgoing request
//!   handler to add an IFC check: the computation label must flow to public
//!   with the module's full privilege.
//!
//! - **Cell reads** (`read_cell`): the cell label must flow to the computation
//!   label.  The module's full privilege is applied automatically — no explicit
//!   endorse parameter.
//!
//! - **Filesystem** access is proxied to the client over a Unix socket. File
//!   writes check that the computation label flows to the channel label
//!   (auto-applying module privilege).
//!
//! The computation label is **immutable** for the duration of execution.

use std::sync::{Arc, Mutex};

use wasmtime_wasi::{IoView, ResourceTable, WasiCtx, WasiView};

use crate::ifc::{Label, Privilege};

// Generate bindings for the custom interfaces (ifc + fs + http).
wasmtime::component::bindgen!({
    path: "wit/cleanroom-ifc.wit",
    world: "runner",
});

pub struct CleanroomState {
    pub table: ResourceTable,
    pub ctx: WasiCtx,

    /// The immutable computation label, set at module spawn time.
    pub label: Label,

    /// The module's privilege (derived from `speaks_for` in the policy).
    pub privilege: Privilege,

    /// The policy containing cell definitions.
    pub policy: Arc<crate::policy::Policy>,

    /// Label of the output channel (derived from the caller's authority).
    pub channel_label: Label,

    /// Client connection for proxying filesystem calls.
    pub client_stream: Option<Arc<Mutex<std::os::unix::net::UnixStream>>>,
}

impl IoView for CleanroomState {
    fn table(&mut self) -> &mut ResourceTable {
        &mut self.table
    }
}

impl WasiView for CleanroomState {
    fn ctx(&mut self) -> &mut WasiCtx {
        &mut self.ctx
    }
}

// ── IFC interface ──────────────────────────────────────────────────

impl self::oak::cleanroom::ifc::Host for CleanroomState {
    fn get_label(&mut self) -> self::oak::cleanroom::ifc::Label {
        self::oak::cleanroom::ifc::Label {
            secrecy: self.label.secrecy_names(),
            integrity: self.label.integrity_names(),
        }
    }

    fn read_cell(&mut self, name: String) -> Option<String> {
        let (value, cell_label) = self.policy.get_cell(&name)?;

        if let Err(e) = cell_label.flows_to_endorsing(&self.label, &self.privilege) {
            log::warn!(
                "cell read denied: \"{name}\" with label {cell_label} \
                 does not flow to computation label {}: {e}",
                self.label
            );
            return None;
        }

        log::info!("cell read: \"{name}\" with label {cell_label}");
        Some(value.clone())
    }
}

// ── HTTP interface ─────────────────────────────────────────────────

impl self::oak::cleanroom::http::Host for CleanroomState {
    /// IFC-gated outgoing HTTP request with automatic privilege.
    ///
    /// The computation label must flow to `Label::public()` with the
    /// module's full privilege applied.  No explicit declassification
    /// parameter — the runtime uses the module's `speaks_for` set.
    fn send_request(
        &mut self,
        request: self::oak::cleanroom::http::HttpRequest,
    ) -> std::result::Result<self::oak::cleanroom::http::HttpResponse, String> {
        use std::io::Read;

        let public = crate::ifc::Label::public();

        if let Err(e) = self.label.flows_to_declassifying(&public, &self.privilege) {
            log::warn!(
                "IFC: blocking HTTP {} to {} — computation {} \
                 does not flow to public: {e}",
                request.method,
                request.url,
                self.label
            );
            return Err(format!("IFC: outbound HTTP blocked — {e}"));
        }

        log::info!("HTTP {} {}", request.method, request.url);

        let mut ureq_request = ureq::request(&request.method, &request.url);
        for (key, value) in &request.headers {
            ureq_request = ureq_request.set(key, value);
        }

        let response = if let Some(body) = request.body {
            ureq_request.send_bytes(&body)
        } else {
            ureq_request.call()
        };

        match response {
            Ok(resp) => {
                let status = resp.status();
                let headers: Vec<(String, String)> = resp
                    .headers_names()
                    .into_iter()
                    .filter_map(|name| resp.header(&name).map(|v| (name, v.to_string())))
                    .collect();
                let mut body = Vec::new();
                resp.into_reader()
                    .read_to_end(&mut body)
                    .map_err(|e| format!("reading response body: {e}"))?;

                Ok(self::oak::cleanroom::http::HttpResponse { status, headers, body })
            }
            Err(ureq::Error::Status(code, resp)) => {
                let mut body = Vec::new();
                resp.into_reader()
                    .read_to_end(&mut body)
                    .map_err(|e| format!("reading error body: {e}"))?;

                Ok(self::oak::cleanroom::http::HttpResponse { status: code, headers: vec![], body })
            }
            Err(e) => Err(format!("HTTP request failed: {e}")),
        }
    }
}

// ── Filesystem proxy ───────────────────────────────────────────────

impl CleanroomState {
    fn send_file_rpc(
        &mut self,
        req: crate::protocol::ServerToClient,
    ) -> std::result::Result<crate::protocol::ClientToServer, String> {
        let client_stream = self.client_stream.clone();
        if let Some(ref stream_lock) = client_stream {
            let mut stream = stream_lock.lock().unwrap();
            crate::protocol::write_message(&mut *stream, &req)
                .map_err(|e| format!("write error: {e}"))?;
            crate::protocol::read_message(&mut *stream).map_err(|e| format!("read error: {e}"))
        } else {
            Err("no client connection".to_string())
        }
    }

    /// Checks whether the computation label flows to the channel label
    /// with the module's full privilege applied.  Used for writes and
    /// deletes that send data back to the caller's sandbox.
    fn check_outbound_flow(&self) -> std::result::Result<(), String> {
        self.label
            .flows_to_declassifying(&self.channel_label, &self.privilege)
            .map_err(|e| e.to_string())
    }
}

impl self::oak::cleanroom::fs::Host for CleanroomState {
    fn read_file(&mut self, path: String) -> std::result::Result<Vec<u8>, String> {
        let resp = self.send_file_rpc(crate::protocol::ServerToClient::FsReadFile { path })?;
        match resp {
            crate::protocol::ClientToServer::FsReadFileResult { data } => {
                data.ok_or_else(|| "file not found".to_string())
            }
            _ => Err("unexpected response from client".to_string()),
        }
    }

    fn write_file(&mut self, path: String, data: Vec<u8>) -> std::result::Result<(), String> {
        self.check_outbound_flow().map_err(|e| format!("blocked writing tainted data: {e}"))?;

        let resp =
            self.send_file_rpc(crate::protocol::ServerToClient::FsWriteFile { path, data })?;
        match resp {
            crate::protocol::ClientToServer::FsWriteFileResult { success } => {
                if success {
                    Ok(())
                } else {
                    Err("failed to write file".to_string())
                }
            }
            _ => Err("unexpected response from client".to_string()),
        }
    }

    fn delete_file(&mut self, path: String) -> std::result::Result<(), String> {
        self.check_outbound_flow().map_err(|e| format!("blocked deleting tainted data: {e}"))?;

        let resp = self.send_file_rpc(crate::protocol::ServerToClient::FsDeleteFile { path })?;
        match resp {
            crate::protocol::ClientToServer::FsDeleteFileResult { success } => {
                if success {
                    Ok(())
                } else {
                    Err("failed to delete file".to_string())
                }
            }
            _ => Err("unexpected response from client".to_string()),
        }
    }

    fn list_directory(&mut self, path: String) -> std::result::Result<Vec<String>, String> {
        let resp = self.send_file_rpc(crate::protocol::ServerToClient::FsListDirectory { path })?;
        match resp {
            crate::protocol::ClientToServer::FsListDirectoryResult { entries } => Ok(entries),
            _ => Err("unexpected response from client".to_string()),
        }
    }
}
