//
// Copyright 2021 The Project Oak Authors
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

//! Test utilities to help with unit testing of Oak-Functions SDK code.

use anyhow::Context;
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Response,
};
use log::info;
use prost::Message;
use std::{
    collections::HashMap,
    convert::Infallible,
    net::{Ipv6Addr, SocketAddr},
    path::PathBuf,
    process::Command,
    sync::{Arc, Mutex},
};

// TODO(#1965): Move this and the similar function in `oak/sdk` to a common crate.
/// Uses cargo to compile a Rust manifest to Wasm bytes.
pub fn compile_rust_wasm(
    manifest_path: &str,
    module_wasm_file_name: &str,
) -> anyhow::Result<Vec<u8>> {
    let mut module_path = PathBuf::from(manifest_path);
    module_path.pop();
    module_path.push("bin");

    let args = vec![
        // `--out-dir` is unstable and requires `-Zunstable-options`.
        "-Zunstable-options".to_string(),
        "build".to_string(),
        "--release".to_string(),
        "--target=wasm32-unknown-unknown".to_string(),
        format!("--manifest-path={}", manifest_path),
        // Use a fixed target directory, because `--target-dir` influences SHA256 hash
        // of Wasm module.  Target directory should also be synchronized with
        // `--target-dir` used in [`oak_tests::compile_rust_wasm`] in order to have
        // same SHA256 hashes.
        format!("--target-dir={}", {
            let mut target_dir = PathBuf::from(manifest_path);
            target_dir.pop();
            target_dir.push("target");
            target_dir.to_str().expect("Invalid target dir").to_string()
        }),
        format!(
            "--out-dir={}",
            module_path
                .to_str()
                .expect("Invalid target dir")
                .to_string()
        ),
    ];

    Command::new("cargo")
        .args(args)
        .env_remove("RUSTFLAGS")
        .spawn()
        .context("Couldn't spawn cargo build")?
        .wait()
        .context("Couldn't wait for cargo build to finish")?;

    module_path.push(module_wasm_file_name);

    info!("Compiled Wasm module path: {:?}", module_path);

    std::fs::read(module_path).context("Couldn't read compiled module")
}

/// A mock implementation of a static server that always returns the same configurable response for
/// any incoming HTTP request.
#[derive(Default)]
pub struct MockStaticServer {
    response_body: Arc<Mutex<Vec<u8>>>,
}

impl MockStaticServer {
    /// Sets the content of the response body to return for any request.
    pub fn set_response_body(&self, response_body: Vec<u8>) {
        *self
            .response_body
            .lock()
            .expect("could not lock response body mutex") = response_body;
    }

    /// Starts serving, listening on the provided port.
    pub async fn serve(&self, port: u16) {
        let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, port));
        let response_body = self.response_body.clone();
        let server = hyper::Server::bind(&address).serve(make_service_fn(|_conn| {
            let response_body = response_body.clone();
            async {
                Ok::<_, Infallible>(service_fn(move |_req| {
                    let response_body = response_body.clone();
                    async move {
                        let response_body: Vec<u8> = response_body
                            .lock()
                            .expect("could not lock response body mutex")
                            .clone();
                        Ok::<_, Infallible>(Response::new(Body::from(response_body)))
                    }
                }))
            }
        }));
        server.await.unwrap();
    }
}

/// Serializes the provided map as a contiguous buffer of length-delimited protobuf messages of type
/// [`Entry`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/lookup_data.proto).
pub fn serialize_entries(entries: HashMap<Vec<u8>, Vec<u8>>) -> Vec<u8> {
    let mut buf = Vec::new();
    for (key, value) in entries.into_iter() {
        let entry_proto = oak_functions_abi::proto::Entry { key, value };
        entry_proto
            .encode_length_delimited(&mut buf)
            .expect("could not encode entry as length delimited");
    }
    buf
}
