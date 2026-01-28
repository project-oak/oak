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

#![feature(test)]

extern crate test;

use std::{
    cell::RefCell,
    net::{SocketAddr, TcpListener, TcpStream},
    rc::Rc,
    sync::Arc,
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};

use criterion::{criterion_group, criterion_main, Criterion};
use message_stream_client::{MessageStream, NoiseMessageStream};
use oak_channel::message::RequestMessage;
use oak_file_utils::data_path;
use oak_launcher_utils::launcher;

type ServerStreamCreator = Arc<dyn Fn(TcpStream) -> Box<dyn MessageStream> + Send + Sync + 'static>;

pub struct OakClientChannelMessageStream {
    oak_client_channel: Rc<RefCell<oak_channel::client::ClientChannelHandle>>,
}

impl OakClientChannelMessageStream {
    pub fn new(
        oak_client_channel: &Rc<RefCell<oak_channel::client::ClientChannelHandle>>,
    ) -> OakClientChannelMessageStream {
        OakClientChannelMessageStream { oak_client_channel: oak_client_channel.clone() }
    }
}
// Even though Channel implements Read + Write, the returned `Box<dyn Channel>`
// does not satisfy the required trait boundaries above. I am not quite sure
// why, or if this is even addressable.
impl MessageStream for OakClientChannelMessageStream {
    fn read_message(&mut self) -> Vec<u8> {
        let (msg, _timer) =
            self.oak_client_channel.borrow_mut().read_response().expect("failed to read message");
        msg.body
    }

    fn send_message(&mut self, msg: &[u8]) {
        self.oak_client_channel
            .borrow_mut()
            .write_request(RequestMessage { invocation_id: 0, body: msg.to_vec() })
            .expect("failed to read message");
    }
}

fn start_tcp_server(stream_creator: ServerStreamCreator) -> (SocketAddr, JoinHandle<()>) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("failed to bind server");
    let addr = listener.local_addr().expect("failed to get local address");
    let stream_creator = stream_creator.clone();
    let handle = thread::spawn(move || loop {
        let (tcp_stream, _) = listener.accept().expect("failed to receive connection");
        let stream = &mut stream_creator(tcp_stream);

        let read_msg = stream.read_message();
        if read_msg == b"exit" {
            break;
        }
        stream.send_message(&read_msg);
    });
    (addr, handle)
}

async fn start_rk_enclave_server(
    mode: &[u8],
) -> (Box<dyn launcher::GuestInstance>, Rc<RefCell<oak_channel::client::ClientChannelHandle>>) {
    let oak_restricted_kernel_orchestrator_app_path =
        data_path("enclave_apps/oak_orchestrator/oak_orchestrator");

    let initial_data_version = launcher::InitialDataVersion::V1;
    let communication_channel = launcher::CommunicationChannel::VirtioConsole;
    let kernel = data_path(
        "oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin",
    );

    let app = data_path("oak_benchmarks/oak_paper/crypto_channel/enclave_app");
    let params = launcher::Params {
        kernel,
        vmm_binary: which::which("qemu-system-x86_64").unwrap(),
        app_binary: Some(app),
        bios_binary: data_path("stage0_bin/stage0_bin"),
        gdb: None,
        initrd: oak_restricted_kernel_orchestrator_app_path,
        memory_size: Some("256M".to_string()),
        pci_passthrough: None,
        initial_data_version,
        communication_channel,
        vm_type: launcher::VmType::Default,
    };
    println!("launcher params: {:?}", params);

    let (guest_instance, _connector_handle) =
        launcher::launch(params).await.expect("failed to launch");

    let oak_client_channel = Rc::new(RefCell::new(oak_channel::client::ClientChannelHandle::new(
        guest_instance.connect().await.expect("couldn't get connector handle"),
    )));

    oak_client_channel
        .borrow_mut()
        .write_request(RequestMessage { invocation_id: 0, body: mode.to_vec() })
        .expect("couldn't write initial request");

    (guest_instance, oak_client_channel)
}

fn create_message(size: usize) -> Vec<u8> {
    let mut message = vec![0u8; size];
    for (i, msg) in message.iter_mut().enumerate() {
        *msg = (i % 256) as u8;
    }
    message
}

const TEST_SIZES: &[usize] = &[1, 100, 10_000, 1_000_000, 100_000_000];

fn benchmark_wrapper(
    sizes: &[usize],
    description: &str,
    c: &mut Criterion,
    mut stream_creator: impl FnMut() -> Box<dyn MessageStream>,
) {
    let mut group = c.benchmark_group(description);

    for size in sizes.iter() {
        group.throughput(criterion::Throughput::Bytes(*size as u64));
        group.bench_with_input(criterion::BenchmarkId::from_parameter(size), size, |b, size| {
            b.iter_custom(|iters| {
                let mut send_total = Duration::from_millis(0);
                let mut recv_total = Duration::from_millis(0);
                for _i in 0..iters {
                    let mut stream = stream_creator();
                    let message = create_message(*size);
                    let start = Instant::now();
                    stream.send_message(message.as_slice());
                    send_total += start.elapsed();
                    let start = Instant::now();
                    let response = stream.read_message();
                    recv_total += start.elapsed();
                    assert_eq!(message, response);
                }
                (send_total + recv_total) / 2
            });
        });
    }

    group.finish();
}

fn plaintext_local_tcp_benchmark(c: &mut Criterion) {
    let (addr, server_handle) =
        start_tcp_server(Arc::new(|tcp_stream: TcpStream| -> Box<dyn MessageStream> {
            Box::new(tcp_stream)
        }));

    benchmark_wrapper(TEST_SIZES, "Local TCP Plaintext Message Exchange", c, || {
        Box::new(TcpStream::connect(addr).expect("couldn't connect to server"))
    });

    let mut stream = TcpStream::connect(addr).expect("couldn't connect to server");
    stream.send_message(b"exit");
    server_handle.join().unwrap();
}

fn new_noise_client_stream(addr: SocketAddr) -> Box<dyn MessageStream> {
    let tcp_stream = TcpStream::connect(addr).expect("couldn't connect to server");
    Box::new(NoiseMessageStream::new_client(tcp_stream))
}

fn noise_local_tcp_benchmark(c: &mut Criterion) {
    let (addr, server_handle) =
        start_tcp_server(Arc::new(|tcp_stream: TcpStream| -> Box<dyn MessageStream> {
            Box::new(NoiseMessageStream::new_server(tcp_stream))
        }));

    benchmark_wrapper(TEST_SIZES, "Local TCP Noise Message Exchange", c, || {
        new_noise_client_stream(addr)
    });

    let mut stream = new_noise_client_stream(addr);
    stream.send_message(b"exit");
    server_handle.join().unwrap();
}

fn plaintext_rk_benchmark(c: &mut Criterion) {
    // Start the enclave app.
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");
    let (guest_instance, oak_client_channel) =
        rt.block_on(async { start_rk_enclave_server(b"plaintext").await });

    benchmark_wrapper(&[1, 1_000_000], "RK Plaintext Message Exchange", c, || {
        Box::new(OakClientChannelMessageStream::new(&oak_client_channel))
    });
    futures::executor::block_on(async { guest_instance.kill().await })
        .expect("failed to kill instance");
}

fn noise_rk_benchmark(c: &mut Criterion) {
    // Start the enclave app.
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");
    let (guest_instance, oak_client_channel) =
        rt.block_on(async { start_rk_enclave_server(b"noise").await });

    benchmark_wrapper(&[1, 1_000_000], "RK Noise Message Exchange", c, || {
        Box::new(NoiseMessageStream::new_client(OakClientChannelMessageStream::new(
            &oak_client_channel,
        )))
    });

    rt.block_on(async { guest_instance.kill().await }).expect("failed to kill instance");
}

criterion_group!(
    benches,
    plaintext_rk_benchmark,
    noise_rk_benchmark,
    plaintext_local_tcp_benchmark,
    noise_local_tcp_benchmark
);
criterion_main!(benches);
