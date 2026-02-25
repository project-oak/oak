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

//! Utilities for end-to-end testing of the Oak Private Memory server.
//!
//! This module provides tools to start the server in different environments
//! (host-based or container-based) and manage its lifecycle during tests.

use std::{
    net::{IpAddr, Ipv4Addr, SocketAddr},
    sync::{Arc, Mutex},
    time::SystemTime,
};

use anyhow::Result;
use oak_containers_launcher::{Args, Launcher, QemuParams, QemuVmType, TrustedApplicationAddress};
pub use oak_private_memory_database::clock::{Clock, SystemClock, system_time_to_timestamp};
use private_memory_server_lib::{
    app,
    app::{ApplicationConfig, run_persistence_service},
};
use runfiles::Runfiles;
use tokio::net::TcpListener;

/// Initializes logging for tests if it hasn't been initialized already.
fn init_logging() {
    let _ = env_logger::builder().is_test(true).try_init();
}

/// Starts a test database server on a random available port.
///
/// Returns the bound socket address and a handle to the spawned task.
pub async fn start_test_database() -> Result<(SocketAddr, tokio::task::JoinHandle<Result<()>>)> {
    let db_addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let db_listener = TcpListener::bind(db_addr).await?;
    let db_addr = db_listener.local_addr()?;
    let db_handle =
        tokio::spawn(private_memory_test_database_server_lib::service::create(db_listener));
    Ok((db_addr, db_handle))
}

/// Starts the Private Memory server in the current process (host mode).
///
/// This function spins up the main application service, a test database
/// service, and the persistence worker.
///
/// Returns the server address and join handles for the spawned tasks.
pub async fn start_server() -> Result<(
    SocketAddr,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<()>,
)> {
    start_server_with_clock(None).await
}

/// Starts the Private Memory server in host mode with an optional custom clock.
///
/// If no clock is provided, the standard [`SystemClock`] is used.
pub async fn start_server_with_clock(
    clock: Option<Arc<dyn Clock>>,
) -> Result<(
    SocketAddr,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<()>,
)> {
    init_logging();

    let (db_addr, db_handle) = start_test_database().await?;

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await?;
    let addr = listener.local_addr()?;

    let application_config = ApplicationConfig { database_service_host: db_addr };

    let metrics = private_memory_server_lib::metrics::get_global_metrics();
    let (persistence_tx, persistence_rx) = tokio::sync::mpsc::unbounded_channel();
    let persistence_join_handle = tokio::spawn(run_persistence_service(persistence_rx));

    let clock = clock.unwrap_or_else(|| Arc::new(SystemClock));

    Ok((
        addr,
        tokio::spawn(app::service::create(
            listener,
            application_config,
            metrics,
            persistence_tx,
            std::sync::Arc::new(attestation_testing::dummy_server_session_config),
            clock,
        )),
        db_handle,
        persistence_join_handle,
    ))
}

/// Starts the Private Memory server inside an Oak Container (container mode).
///
/// This function launches a QEMU VM running the Oak Containers system image and
/// the Private Memory enclave application. It also starts a local test database
/// service and configures QEMU to forward traffic to it.
///
/// Returns the enclave URL, a handle to the database service, and the VM
/// launcher.
pub async fn start_container_server() -> Result<(
    String,                              // Enclave URL
    tokio::task::JoinHandle<Result<()>>, // DB handle
    Launcher,
)> {
    let (db_addr, db_handle) = start_test_database().await?;
    let db_port = db_addr.port();

    // Host IP for the enclave in default network mode.
    let host_ip = Ipv4Addr::new(10, 0, 2, 100);
    let application_config =
        ApplicationConfig { database_service_host: SocketAddr::new(IpAddr::V4(host_ip), db_port) };
    let application_config_bytes = serde_json::to_vec(&application_config)?;

    let vmm_binary = which::which("qemu-system-x86_64").expect("could not find qemu path");
    let r = Runfiles::create().unwrap();
    let system_image = runfiles::rlocation!(r, "oak_containers_system_image/file/downloaded")
        .expect("could not find system image");
    let stage0_binary = runfiles::rlocation!(r, "oak_containers_stage0/file/downloaded")
        .expect("could not find stage0 binary");
    let kernel = runfiles::rlocation!(r, "oak_containers_kernel/file/downloaded")
        .expect("could not find kernel");
    let initrd = runfiles::rlocation!(r, "oak_containers_stage1/file/downloaded")
        .expect("could not find initrd");
    let container_bundle =
        runfiles::rlocation!(r, "_main/bundle.tar").expect("could not find container bundle");

    let args = Args {
        system_image,
        container_bundle,
        application_config: application_config_bytes,
        extra_guest_to_host_ports: vec![db_port],
        qemu_params: QemuParams {
            vmm_binary,
            stage0_binary,
            kernel,
            initrd,
            memory_size: Some("8G".to_owned()),
            num_cpus: 2,
            ramdrive_size: 3_000_000,
            telnet_console: None,
            virtio_guest_cid: None,
            pci_passthrough: None,
            vm_type: QemuVmType::Default,
        },
        communication_channel: oak_containers_launcher::ChannelType::Network,
    };

    let mut launcher = Launcher::create(args).await?;
    let enclave_addr = match launcher.get_trusted_app_address().await? {
        TrustedApplicationAddress::Network(addr) => addr,
        _ => anyhow::bail!("Expected network address"),
    };

    Ok((format!("http://{enclave_addr}"), db_handle, launcher))
}

/// Represents the active test backend and its associated resources.
pub enum TestBackend {
    /// Server is running as a local task in the host process.
    Host {
        server_handle: tokio::task::JoinHandle<Result<()>>,
        db_handle: tokio::task::JoinHandle<Result<()>>,
        persistence_handle: tokio::task::JoinHandle<()>,
    },
    /// Server is running inside a QEMU VM.
    Container { launcher: Launcher, db_handle: tokio::task::JoinHandle<Result<()>> },
}

/// A unified context for end-to-end tests that abstracts over the execution
/// environment.
///
/// It uses the `OAK_E2E_BACKEND` environment variable to determine whether to
/// start the server in `host` mode (default) or `container` mode.
pub struct TestContext {
    /// The base URL of the running server.
    pub url: String,
    /// The specific backend handles for the current session.
    pub backend: TestBackend,
}

impl TestContext {
    /// Sets up a new test environment by starting the server in the appropriate
    /// mode.
    pub async fn setup() -> Result<Self> {
        if std::env::var("OAK_E2E_BACKEND").as_deref() == Ok("container") {
            let (url, db_handle, launcher) = start_container_server().await?;
            Ok(Self { url, backend: TestBackend::Container { launcher, db_handle } })
        } else {
            let (addr, server_handle, db_handle, persistence_handle) = start_server().await?;
            Ok(Self {
                url: format!("http://{}", addr),
                backend: TestBackend::Host { server_handle, db_handle, persistence_handle },
            })
        }
    }

    /// Sets up a new test environment with a custom clock.
    ///
    /// Note: Custom clocks are currently only supported in `host` mode. In
    /// `container` mode, the custom clock is ignored and the server uses
    /// the VM's system time.
    pub async fn setup_with_clock(clock: Arc<dyn Clock>) -> Result<Self> {
        if std::env::var("OAK_E2E_BACKEND").as_deref() == Ok("container") {
            // MockClock is ignored in container mode
            Self::setup().await
        } else {
            let (addr, server_handle, db_handle, persistence_handle) =
                start_server_with_clock(Some(clock)).await?;
            Ok(Self {
                url: format!("http://{}", addr),
                backend: TestBackend::Host { server_handle, db_handle, persistence_handle },
            })
        }
    }

    /// Returns true if the server is running in host mode.
    pub fn is_host(&self) -> bool {
        matches!(self.backend, TestBackend::Host { .. })
    }

    /// Cleans up the test environment, ensuring that the server and any
    /// associated VMs are properly terminated.
    pub async fn teardown(self) {
        if let TestBackend::Container { mut launcher, .. } = self.backend {
            launcher.kill().await;
        }
    }
}

/// A mock implementation of the [`Clock`] trait that returns a fixed,
/// controllable time.
pub struct MockClock {
    /// The current time stored in the mock.
    pub time: Arc<Mutex<SystemTime>>,
}

impl MockClock {
    /// Creates a new mock clock initialized to the given time.
    pub fn new(time: SystemTime) -> Self {
        Self { time: Arc::new(Mutex::new(time)) }
    }

    /// Updates the time returned by this clock.
    pub fn set_time(&self, time: SystemTime) {
        let mut guard = self.time.lock().unwrap();
        *guard = time;
    }
}

impl Clock for MockClock {
    /// Returns the current mock time.
    fn now(&self) -> SystemTime {
        let guard = self.time.lock().unwrap();
        *guard
    }
}
