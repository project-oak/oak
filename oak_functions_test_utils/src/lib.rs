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
use log::info;
use nix::unistd::Pid;
use oak_functions_abi::Response;
use oak_functions_client::Client;
use prost::Message;
use std::{
    collections::HashMap, future::Future, io::Write, pin::Pin, process::Command, task::Poll,
    time::Duration,
};
use tokio::{sync::oneshot, task::JoinHandle};

/// Returns the path to the Wasm file produced by compiling the provided `Cargo.toml` file.
fn build_wasm_module_path(metadata: &cargo_metadata::Metadata) -> String {
    let package_name = &metadata.root_package().unwrap().name;
    // Keep this in sync with `/xtask/src/main.rs`.
    format!("{}/bin/{package_name}.wasm", metadata.workspace_root)
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
        format!("--manifest-path={manifest_path}"),
    ];

    if release {
        args.push("--release".to_string());
    }

    Command::new("cargo")
        .args(args)
        .env_remove("RUSTFLAGS")
        .spawn()
        .context("couldn't spawn cargo build")?
        .wait()
        .context("couldn't wait for cargo build to finish")?;

    let module_path = build_wasm_module_path(&metadata);
    info!("Compiled Wasm module path: {:?}", module_path);

    std::fs::read(module_path).context("couldn't read compiled module")
}

/// Serializes the provided map as a contiguous buffer of length-delimited protobuf messages of type
/// [`Entry`](https://github.com/project-oak/oak/blob/main/oak_functions/proto/lookup_data.proto).
pub fn serialize_entries(entries: HashMap<Vec<u8>, Vec<u8>>) -> Vec<u8> {
    let mut buf = Vec::new();
    for (key, value) in entries.into_iter() {
        let entry_proto = oak_functions_abi::proto::Entry { key, value };
        entry_proto
            .encode_length_delimited(&mut buf)
            .expect("couldn't encode entry as length delimited");
    }
    buf
}

pub fn write_to_temp_file(content: &[u8]) -> tempfile::NamedTempFile {
    let mut file = tempfile::NamedTempFile::new().expect("couldn't create temp file");
    file.write_all(content)
        .expect("couldn't write content to temp file");
    file
}

pub fn free_port() -> u16 {
    port_check::free_local_port().expect("couldn't pick free local port")
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
            .expect("couldn't send signal on termination channel");
        self.join_handle
            .await
            .expect("couldn' wait for background task to terminate")
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

/// Builds the crate identified by the given package name (as per the `name` attribute in a
/// Cargo.toml file included in the root cargo workspace) as a Linux binary, and returns the path of
/// the resulting binary.
fn build_rust_crate_linux(crate_name: &str) -> anyhow::Result<String> {
    duct::cmd!(
        "cargo",
        "build",
        "--target=x86_64-unknown-linux-musl",
        "--release",
        format!("--package={crate_name}"),
    )
    .dir(env!("WORKSPACE_ROOT"))
    .run()
    .context(format!("couldn't compile {crate_name}"))?;
    Ok(format!(
        "{}target/x86_64-unknown-linux-musl/release/{crate_name}",
        env!("WORKSPACE_ROOT")
    ))
}

/// Builds the crate identified by the given package name (as per the `name` attribute in a
/// Cargo.toml file included in the root cargo workspace) as a Wasm module, and returns the path of
/// the resulting binary.
pub fn build_rust_crate_wasm(crate_name: &str) -> anyhow::Result<String> {
    duct::cmd!(
        "cargo",
        "build",
        "--target=wasm32-unknown-unknown",
        "--release",
        format!("--package={crate_name}"),
    )
    .dir(env!("WORKSPACE_ROOT"))
    .run()
    .context(format!("couldn't compile {crate_name}"))?;
    Ok(format!(
        "{}target/wasm32-unknown-unknown/release/{crate_name}.wasm",
        env!("WORKSPACE_ROOT"),
    ))
}

/// Starts an instance of the Oak Functions server running in the background, listening on the
/// provided port, and running the provided Wasm module, with the provided data available for
/// lookup.
///
/// Returns a handle to the background process.
pub fn create_and_start_oak_functions_server(
    server_port: u16,
    wasm_module_path: &str,
    lookup_data_path: &str,
) -> anyhow::Result<duct::ReaderHandle> {
    let oak_functions_launcher_path = build_rust_crate_linux("oak_functions_launcher")?;
    let oak_functions_linux_fd_bin_path = build_rust_crate_linux("oak_functions_linux_fd_bin")?;

    let handle = duct::cmd!(
        oak_functions_launcher_path,
        format!("--wasm={wasm_module_path}"),
        format!("--port={server_port}"),
        format!("--lookup-data={lookup_data_path}"),
        "native",
        format!("--app-binary={oak_functions_linux_fd_bin_path}"),
    )
    .dir(env!("WORKSPACE_ROOT"))
    .reader()
    .context("couldn't run oak_functions_launcher")?;
    Ok(handle)
}

/// Kills all the processes identified by the provided handle.
///
/// First tries to send them a `SIGINT` signal, then, if they are still running, it sends them a
/// `SIGKILL` signal.
pub fn kill_process(handle: duct::ReaderHandle) {
    handle.pids().iter().for_each(|pid| {
        nix::sys::signal::kill(Pid::from_raw(*pid as i32), nix::sys::signal::SIGINT).unwrap()
    });
    // Wait for the process to terminate cleanly, then forcefully kill it.
    std::thread::sleep(Duration::from_secs(2));
    handle.kill().unwrap();
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

pub async fn make_request(port: u16, request_body: &[u8]) -> Vec<u8> {
    let uri = format!("http://localhost:{port}/");

    // Create client
    let mut client = Client::new(&uri).await.expect("couldn't create client");

    client
        .invoke(request_body)
        .await
        .expect("error while awaiting response")
}

// Assert that string value of the body of the given response matches the expected string.
pub fn assert_response_body(response: Response, expected: &str) {
    let body = response.body().unwrap();
    assert_eq!(
        std::str::from_utf8(body).expect("couldn't convert response body from utf8"),
        expected
    )
}
