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
    Body,
};
use log::info;
use oak_functions_abi::{Request, Response};

use oak_functions_client::Client;
use prost::Message;
use std::{
    collections::HashMap,
    convert::Infallible,
    future::Future,
    net::{Ipv6Addr, SocketAddr},
    pin::Pin,
    process::Command,
    sync::{Arc, Mutex},
    task::Poll,
    time::Duration,
};
use tokio::{sync::oneshot, task::JoinHandle};

/// Returns the path to the Wasm file produced by compiling the provided `Cargo.toml` file.
fn build_wasm_module_path(metadata: &cargo_metadata::Metadata) -> String {
    let package_name = &metadata.root_package().unwrap().name;
    // Keep this in sync with `/xtask/src/main.rs`.
    format!("{}/bin/{}.wasm", metadata.workspace_root, package_name)
}

/// Uses cargo to compile a Rust manifest to Wasm bytes.
pub fn compile_rust_wasm(manifest_path: &str, release: bool) -> anyhow::Result<Vec<u8>> {
    let metadata = cargo_metadata::MetadataCommand::new()
        .manifest_path(manifest_path)
        .exec()
        .unwrap();
    // Keep this in sync with `/xtask/src/main.rs`.
    // Keep this in sync with `/sdk/rust/oak_tests/src/lib.rs`.
    let mut args = vec![
        // `--out-dir` is unstable and requires `-Zunstable-options`.
        "-Zunstable-options".to_string(),
        "build".to_string(),
        "--target=wasm32-unknown-unknown".to_string(),
        format!("--target-dir={}/wasm", metadata.target_directory),
        format!("--out-dir={}/bin", metadata.workspace_root),
        format!("--manifest-path={}", manifest_path),
    ];

    if release {
        args.push("--release".to_string());
    }

    Command::new("cargo")
        .args(args)
        .env_remove("RUSTFLAGS")
        .spawn()
        .context("Couldn't spawn cargo build")?
        .wait()
        .context("Couldn't wait for cargo build to finish")?;

    let module_path = build_wasm_module_path(&metadata);
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
    pub async fn serve<F: Future<Output = ()>>(&self, port: u16, terminate: F) {
        let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, port));
        let response_body = self.response_body.clone();
        let server = hyper::Server::bind(&address)
            .serve(make_service_fn(|_conn| {
                let response_body = response_body.clone();
                async {
                    Ok::<_, Infallible>(service_fn(move |_req| {
                        let response_body = response_body.clone();
                        async move {
                            let response_body: Vec<u8> = response_body
                                .lock()
                                .expect("could not lock response body mutex")
                                .clone();
                            Ok::<_, Infallible>(hyper::Response::new(Body::from(response_body)))
                        }
                    }))
                }
            }))
            .with_graceful_shutdown(terminate);
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

pub fn free_port() -> u16 {
    port_check::free_local_port().expect("could not pick free local port")
}

/// Wrapper around a termination signal [`oneshot::Sender`] and the [`JoinHandle`] of the associated
/// background task, created by [`background`].
pub struct Background<T> {
    term_tx: oneshot::Sender<()>,
    join_handle: JoinHandle<T>,
}

impl<T> Background<T> {
    /// Sends the termination signal to the background task and awaits for it to gracefully
    /// terminate.
    ///
    /// This does not guarantee that the background task terminates (e.g. if it ignores the
    /// termination signal), it requires the cooperation of the task in order to work correctly.
    pub async fn terminate_and_join(self) -> T {
        self.term_tx
            .send(())
            .expect("could not send signal on termination channel");
        self.join_handle
            .await
            .expect("could not wait for background task to terminate")
    }
}

/// Executes the provided closure passing to it a [`Term`] instance signalling when to terminate,
/// and spawns the resulting [`Future`] in the background, returning a [`Background`] instance.
pub fn background<Out, F>(f: F) -> Background<Out::Output>
where
    Out: Future + Send + 'static,
    Out::Output: Send + 'static,
    F: FnOnce(Term) -> Out,
{
    let (term_tx, term_rx) = oneshot::channel::<()>();
    let term = Term { rx: term_rx };
    let join_handle = tokio::spawn(f(term));
    Background {
        term_tx,
        join_handle,
    }
}

/// A wrapper around a termination signal [`oneshot::Receiver`].
///
/// This type manually implements [`Future`] in order to be able to be passed to a closure as part
/// of [`background`].
pub struct Term {
    rx: oneshot::Receiver<()>,
}

impl Future for Term {
    type Output = ();
    fn poll(self: Pin<&mut Self>, c: &mut std::task::Context) -> Poll<()> {
        let rx = &mut self.get_mut().rx;
        tokio::pin!(rx);
        match rx.poll(c) {
            Poll::Ready(v) => {
                v.unwrap();
                Poll::Ready(())
            }
            Poll::Pending => Poll::Pending,
        }
    }
}

pub struct TestResult {
    pub elapsed: Duration,
    pub response: Response,
}

pub async fn make_request(port: u16, request_body: &[u8]) -> TestResult {
    let uri = format!("http://localhost:{}/", port);

    // Create client
    let mut client = Client::new(&uri).await.expect("Could not create client");

    let request = Request {
        body: request_body.to_vec(),
    };

    // Send the request and measure time
    let start = std::time::Instant::now();
    let response = client
        .invoke(request)
        .await
        .expect("Error while awaiting response");
    let elapsed = start.elapsed();

    TestResult { elapsed, response }
}

// Assert that string value of the body of the given response matches the expected string.
pub fn assert_response_body(response: Response, expected: &str) {
    let body = response.body().unwrap();
    assert_eq!(
        std::str::from_utf8(body).expect("could not convert response body from utf8"),
        expected
    )
}

/// Create Wasm bytecode from an Oak Functions example.
fn create_wasm_module_bytes_from_example(
    manifest_path_from_examples: &str,
    release: bool,
) -> Vec<u8> {
    let mut manifest_path = std::path::PathBuf::new();
    // WORKSPACE_ROOT is set in .cargo/config.toml.
    manifest_path.push(env!("WORKSPACE_ROOT"));
    manifest_path.push("oak_functions");
    manifest_path.push("examples");
    manifest_path.push(manifest_path_from_examples);
    compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), release)
        .expect("Couldn't read Wasm module")
}

/// Create valid (release) Wasm bytecode for a minimal "echo" module which only uses the Abi
/// functions `read_request` and `write_request`.
pub fn create_echo_wasm_module_bytes() -> Vec<u8> {
    create_wasm_module_bytes_from_example("echo/module/Cargo.toml", true)
}
