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

//! Wasmtime WASI interception for dynamic IFC.
//!
//! This module intercepts WASI filesystem and HTTP operations to
//! enforce Information Flow Control:
//!
//! - **Reads taint**: file opens taint the pc with the path's label.
//! - **Writes are gated**: filesystem writes and HTTP requests are blocked if
//!   the computation is tainted beyond `{local_repo}`.

use std::sync::{Arc, Mutex};

use wasmtime_wasi::{ResourceTable, WasiCtx, WasiView};

use crate::ifc::ComputationLabel;

// Generate bindings for our custom IFC interface.
wasmtime::component::bindgen!({
    path: "wit/cleanroom-ifc.wit",
    world: "runner",
});

// Stub implementation of standard wasi filesystem to find missing methods using
// rustc.
// Custom Filesystem ABI implementation will be added here.

pub struct CleanroomState {
    pub table: ResourceTable,
    pub ctx: WasiCtx,
    pub http_ctx: wasmtime_wasi_http::WasiHttpCtx,
    pub pc: Arc<Mutex<ComputationLabel>>,
    pub policy: std::sync::Arc<crate::policy::Policy>,
    pub privilege: crate::ifc::DeclassificationPrivilege,

    /// Client connection to the server for proxying custom fs calls.
    pub client_stream: Option<Arc<Mutex<std::os::unix::net::UnixStream>>>,
}

impl WasiView for CleanroomState {
    fn table(&mut self) -> &mut ResourceTable {
        &mut self.table
    }

    fn ctx(&mut self) -> &mut WasiCtx {
        &mut self.ctx
    }
}

// Implement the generated Host trait for our IFC interface.
impl self::oak::cleanroom::ifc::Host for CleanroomState {
    fn get_label(&mut self) -> Vec<String> {
        if let Ok(pc) = self.pc.lock() {
            pc.current_label().category_names().iter().cloned().collect()
        } else {
            vec![]
        }
    }

    fn declassify(&mut self, categories: Vec<String>) -> bool {
        if let Ok(mut pc) = self.pc.lock() {
            pc.declassify(&categories, &self.privilege).is_ok()
        } else {
            false
        }
    }

    fn get_cell(&mut self, name: String) -> Option<String> {
        if let Some((value, label)) = self.policy.get_cell(&name) {
            if let Ok(mut pc) = self.pc.lock() {
                pc.observe(label);
            }
            Some(value.clone())
        } else {
            None
        }
    }
}

impl wasmtime_wasi_http::WasiHttpView for CleanroomState {
    fn ctx(&mut self) -> &mut wasmtime_wasi_http::WasiHttpCtx {
        &mut self.http_ctx
    }

    fn table(&mut self) -> &mut ResourceTable {
        &mut self.table
    }

    /// IFC-gated outgoing HTTP.
    ///
    /// Blocks the request if the computation is tainted.  Outbound
    /// HTTP is a public channel — the module must declassify all
    /// categories before making network requests.
    fn send_request(
        &mut self,
        request: http::Request<wasmtime_wasi_http::body::HyperOutgoingBody>,
        config: wasmtime_wasi_http::types::OutgoingRequestConfig,
    ) -> wasmtime_wasi_http::HttpResult<wasmtime_wasi_http::types::HostFutureIncomingResponse> {
        let channel = crate::ifc::Label::public();
        {
            let pc = self.pc.lock().unwrap();
            if let Err(excess) = pc.current_label().flows_to(&channel) {
                log::warn!("IFC: blocking HTTP request: {excess}");
                return Err(wasmtime_wasi_http::bindings::http::types::ErrorCode::InternalError(
                    Some(format!("IFC: outbound HTTP blocked — {excess}")),
                )
                .into());
            }
        } // release lock before delegating

        Ok(wasmtime_wasi_http::types::default_send_request(request, config))
    }
}

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
}

impl self::oak::cleanroom::fs::Host for CleanroomState {
    fn read_file(&mut self, path: String) -> std::result::Result<Vec<u8>, String> {
        let resp = self.send_file_rpc(crate::protocol::ServerToClient::FsReadFile { path })?;
        match resp {
            crate::protocol::ClientToServer::FsReadFileResult { data } => {
                let mut pc = self.pc.lock().unwrap();
                pc.observe(&crate::ifc::Label::category("local_repo"));
                Ok(data)
            }
            _ => Err("unexpected response from client".to_string()),
        }
    }

    fn write_file(&mut self, path: String, data: Vec<u8>) -> std::result::Result<(), String> {
        let pc = self.pc.lock().unwrap();
        let destination_label = crate::ifc::Label::category("local_repo");
        if let Err(e) = pc.current_label().flows_to(&destination_label) {
            return Err(format!("blocked writing tainted data: {e}"));
        }
        drop(pc); // Release lock before RPC!

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
        let pc = self.pc.lock().unwrap();
        let destination_label = crate::ifc::Label::category("local_repo");
        if let Err(e) = pc.current_label().flows_to(&destination_label) {
            return Err(format!("blocked deleting tainted data: {e}"));
        }
        drop(pc); // Release lock before RPC!

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
