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

//! Test utilities to help with unit testing of Oak Functions code.

use std::{
    collections::HashMap,
    env,
    ffi::{OsStr, OsString},
    future::Future,
    io::Write,
    path::{Path, PathBuf},
    pin::Pin,
    process::Stdio,
    task::Poll,
};

use command_group::stdlib::CommandGroup;
use http::uri::Uri;
use oak_client::verifier::InsecureAttestationVerifier;
use oak_file_utils::data_path;
use oak_functions_abi::Response;
use oak_functions_client::OakFunctionsClient;
use prost::Message;
use tokio::{sync::oneshot, task::JoinHandle};
use ubyte::ByteUnit;

/// Serializes the provided map as a contiguous buffer of length-delimited
/// protobuf messages of type [`Entry`](https://github.com/project-oak/oak/blob/main/proto/oak_functions/lookup_data.proto).
pub fn serialize_entries(entries: HashMap<Vec<u8>, Vec<u8>>) -> Vec<u8> {
    let mut buf = Vec::new();
    for (key, value) in entries.into_iter() {
        let entry_proto = oak_proto_rust::oak::functions::lookup_data::Entry { key, value };
        entry_proto
            .encode_length_delimited(&mut buf)
            .expect("couldn't encode entry as length delimited");
    }
    buf
}

// Create lookup data entries mapping keys to themselves which, when chunked,
// will be chunked to chunk_count chunks of max_chunk_size.
pub fn create_test_lookup_data(
    max_chunk_size: ByteUnit,
    chunk_count: u32,
) -> HashMap<Vec<u8>, Vec<u8>> {
    let mut entries = std::collections::HashMap::new();

    let entry_size = ByteUnit::Byte(10);
    // This has to be consistent with the overhead set in chunking up lookup data.
    let entry_overhead = ByteUnit::Byte(10);
    let chunk_overhead = ByteUnit::Byte(50);
    let max_entries_by_chunk =
        ((max_chunk_size - chunk_overhead) / (entry_size + entry_overhead)).as_u64() as u32;

    for i in 0..(max_entries_by_chunk * chunk_count) {
        // Pad to 5 bytes to have 10 byte entries
        let n = format!("{:05}", i).into_bytes();
        entries.insert(n.clone(), n);
    }
    entries
}

pub fn write_to_temp_file(content: &[u8]) -> tempfile::NamedTempFile {
    let mut file = tempfile::NamedTempFile::new_in(env::var("TEST_TMPDIR").unwrap())
        .expect("couldn't create temp file");
    file.write_all(content).expect("couldn't write content to temp file");
    file
}

pub fn free_port() -> u16 {
    port_check::free_local_port().expect("couldn't pick free local port")
}

/// Wrapper around a termination signal [`oneshot::Sender`] and the
/// [`JoinHandle`] of the associated background task, created by [`background`].
pub struct Background<T> {
    term_tx: oneshot::Sender<()>,
    join_handle: JoinHandle<T>,
}

impl<T> Background<T> {
    /// Sends the termination signal to the background task and awaits for it to
    /// gracefully terminate.
    ///
    /// This does not guarantee that the background task terminates (e.g. if it
    /// ignores the termination signal), it requires the cooperation of the
    /// task in order to work correctly.
    pub async fn terminate_and_join(self) -> T {
        self.term_tx.send(()).expect("couldn't send signal on termination channel");
        self.join_handle.await.expect("couldn' wait for background task to terminate")
    }
}

/// Executes the provided closure passing to it a [`Term`] instance signalling
/// when to terminate, and spawns the resulting [`Future`] in the background,
/// returning a [`Background`] instance.
pub fn background<Out, F>(f: F) -> Background<Out::Output>
where
    Out: Future + Send + 'static,
    Out::Output: Send + 'static,
    F: FnOnce(Term) -> Out,
{
    let (term_tx, term_rx) = oneshot::channel::<()>();
    let term = Term { rx: term_rx };
    let join_handle = tokio::spawn(f(term));
    Background { term_tx, join_handle }
}

/// A wrapper around a termination signal [`oneshot::Receiver`].
///
/// This type manually implements [`Future`] in order to be able to be passed to
/// a closure as part of [`background`].
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

// Assert that string value of the body of the given response matches the
// expected string.
pub fn assert_response_body(response: Response, expected: &str) {
    let body = response.body().unwrap();
    assert_eq!(
        std::str::from_utf8(body).expect("couldn't convert response body from utf8"),
        expected
    )
}

macro_rules! arg {
    ($($a:expr),*) => {
        {
            let mut result = OsString::new();
            $(result.push($a);)*
            result
        }
    };
}

/// Runs the specified example as a background task. Returns a reference to the
/// running server and the port on which the server is listening.
pub fn run_oak_functions_containers_example_in_background(
    wasm_path: impl AsRef<Path>,
    lookup_data_path: impl AsRef<Path>,
    communication_channel: &str,
    uri: Uri,
) -> BackgroundHandle {
    eprintln!("using Wasm module {:?}", wasm_path.as_ref());

    let wasm_path = data_path(wasm_path);
    let launch_bin =
        data_path("oak_functions_containers_launcher/oak_functions_containers_launcher");
    let qemu = which::which("qemu-system-x86_64").expect("QEMU binary not found");
    let stage0_bin = data_path("stage0_bin/stage0_bin");
    let kernel = data_path("oak_containers/kernel/bzImage");
    let initrd = data_path("oak_containers/stage1_bin/stage1.cpio");
    let system_image = data_path("oak_containers/system_image/oak_containers_system_image.tar.xz");
    let container_bundle = data_path("oak_functions_containers_app/bundle.tar");
    let lookup_data_path = data_path(lookup_data_path);
    let ramdrive_size = 1000000;
    let memory_size = "2G";
    let virtio_guest_cid = nix::unistd::gettid();

    let mut args: Vec<OsString> = vec![
        "--map-root-user".into(), // run as root in the namespace so we can create TAP device
    ];
    let mut commands: Vec<OsString> = vec![];

    if communication_channel.starts_with("tap") {
        // TAP network gets a network namespace, so that we could have a `oak0`
        // interface.
        args.push("--net".into()); // create a new network namespace
        commands.push("ip link set lo up".into());
        commands.push("ip tuntap add dev oak0 mode tap".into());
        commands.push("ip addr flush dev oak0".into());

        if communication_channel == "tap" {
            commands.push("ip addr add 10.0.2.100/24 dev oak0".into());
        } else {
            commands.push("ip addr add fdd2:a994:f3c5:1:10:0:2:64/64 dev oak0 nodad".into());
        }
        commands.push("ip link set dev oak0 up".into());
    }
    if communication_channel == "virtio-vsock" {
        // virtio-vsock: you only get a loopback interface. Ideally, not even that.
        args.push("--net".into());
        commands.push("ip link set lo up".into());
    }

    // This is a rather inconvenient way of doing it, but `write!` and `format!`
    // don't know how to deal with OsString-s.
    let mut cmd: OsString = OsString::new();
    cmd.push(launch_bin);
    cmd.push(" --vmm-binary=");
    cmd.push(qemu);
    cmd.push(" --stage0-binary=");
    cmd.push(stage0_bin);
    cmd.push(" --kernel=");
    cmd.push(kernel);
    cmd.push(" --initrd=");
    cmd.push(initrd);
    cmd.push(" --system-image=");
    cmd.push(system_image);
    cmd.push(" --container-bundle=");
    cmd.push(container_bundle);
    cmd.push(format!(" --ramdrive-size={ramdrive_size}"));
    cmd.push(format!(" --memory-size={memory_size}"));
    cmd.push(" --wasm=");
    cmd.push(wasm_path);
    cmd.push(format!(" --port={uri}"));
    cmd.push(" --lookup-data=");
    cmd.push(lookup_data_path);
    cmd.push(format!(" --virtio-guest-cid={virtio_guest_cid}"));
    cmd.push(format!(" --communication-channel={communication_channel}"));
    commands.push(cmd);
    let commands = commands.join(OsStr::new(";"));

    args.push("bash".into());
    args.push("-c".into());
    args.push(commands);

    let child = std::process::Command::new(
        which::which("unshare").expect("could not find `unshare` binary"),
    )
    .args(args)
    .group_spawn()
    .expect("didn't start oak functions containers launcher");
    BackgroundHandle(child)
}

/// A wrapper around a child process that kills it when its dropped.
pub struct BackgroundHandle(pub command_group::GroupChild);

impl std::ops::Drop for BackgroundHandle {
    fn drop(&mut self) {
        self.0.kill().expect("Couldn't kill command group")
    }
}

/// Runs the specified example as a background task. Returns a reference to the
/// running server and the port on which the server is listening.
pub fn run_oak_functions_example_in_background(
    wasm_path: &str,
    lookup_data_path: &str,
) -> (BackgroundHandle, Uri) {
    eprintln!("using Wasm module {}", wasm_path);

    let port = portpicker::pick_unused_port().expect("failed to pick a port");
    eprintln!("using port {}", port);

    let stage0_bin = data_path("stage0_bin/stage0_bin");
    let kernel = data_path(
        "oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin",
    );

    let child =
        std::process::Command::new(data_path("oak_functions_launcher/oak_functions_launcher"))
            .args(vec![
                arg!("--bios-binary=", stage0_bin),
                arg!("--kernel=", kernel),
                arg!(
                    "--vmm-binary=",
                    which::which("qemu-system-x86_64").unwrap().to_str().unwrap()
                ),
                arg!(
                    "--app-binary=",
                    data_path("enclave_apps/oak_functions_enclave_app/oak_functions_enclave_app")
                ),
                arg!("--initrd=", data_path("enclave_apps/oak_orchestrator/oak_orchestrator")),
                arg!("--wasm=", wasm_path),
                arg!("--lookup-data=", lookup_data_path),
                arg!("--port=", port.to_string()),
                arg!("--memory-size=", "256M"),
            ])
            .stdout(Stdio::piped())
            .group_spawn()
            .expect("didn't start oak functions launcher");

    (BackgroundHandle(child), format!("http://localhost:{port}").try_into().unwrap())
}

pub fn run_java_client(addr: &str) -> std::io::Result<std::process::Output> {
    std::process::Command::new(
        PathBuf::from("java/src/main/java/com/google/oak/client/oak_functions_client")
            .join("oak_functions_client"),
    )
    .arg(addr)
    .output()
}

pub fn run_cc_client(addr: &str, request: &str) -> std::io::Result<std::process::Output> {
    std::process::Command::new(PathBuf::from("cc/client").join("cli"))
        .arg(addr)
        .arg(request)
        .output()
}

/// Whether to skip the test. For instance, GitHub Actions does not support KVM,
/// so we cannot run tests that require nested virtualization.
pub fn skip_test() -> bool {
    std::env::var("OAK_KVM_TESTS").unwrap_or_default().to_lowercase() == "skip"
}

/// Periodically try to create an OakFunctionsClient until it works.
///
/// It will give up completely after `connection_timeout`
pub async fn create_client(
    uri: Uri,
    connection_timeout: std::time::Duration,
) -> OakFunctionsClient {
    let interval = std::time::Duration::from_secs(5);
    let attempts = connection_timeout.div_duration_f32(interval) as u32;
    for _ in 1..attempts {
        let client_result =
            OakFunctionsClient::new(uri.clone(), &InsecureAttestationVerifier {}).await;

        match client_result {
            Ok(client) => return client,
            Err(e) => {
                println!("Client not yet ready: {e:?}");
                // Wait for the server to start up.
                tokio::time::sleep(interval).await;
            }
        };
    }
    panic!("Failed to create client");
}
