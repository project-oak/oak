//
// Copyright 2023 The Project Oak Authors
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

pub mod proto {
    pub mod oak {
        pub mod containers {
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.containers");
        }
        pub use oak_crypto::proto::oak::crypto;
        pub use oak_remote_attestation::proto::oak::{attestation, session};
    }
}

mod qemu;
mod server;

use crate::proto::oak::session::v1::{
    AttestationBundle, AttestationEndorsement, AttestationEvidence,
};
use anyhow::Context;
use clap::Parser;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use tokio::{
    net::TcpListener,
    sync::oneshot::{channel, Receiver, Sender},
    task::JoinHandle,
    time::{timeout, Duration},
};

/// The local IP address assigned to the VM guest.
const VM_LOCAL_ADDRESS: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 2, 15));

/// The local port that the VM guest should be listening on.
const VM_LOCAL_PORT: u16 = 8080;

/// The local address that will be forwarded by the VMM to the guest's IP adress.
const PROXY_ADDRESS: Ipv4Addr = Ipv4Addr::LOCALHOST;

/// Number of seconds to wait for the VM to start up.
const VM_START_TIMEOUT: u64 = 300;

#[derive(Parser, Debug)]
#[group(skip)]
pub struct Args {
    #[arg(long, required = true, value_parser = path_exists,)]
    system_image: std::path::PathBuf,
    #[arg(long, required = true, value_parser = path_exists,)]
    container_bundle: std::path::PathBuf,
    #[arg(long, value_parser = path_exists,)]
    application_config: Option<std::path::PathBuf>,
    #[command(flatten)]
    qemu_params: qemu::Params,
}

impl Args {
    pub fn default_for_test() -> Self {
        let system_image = format!(
            "{}oak_containers_system_image/target/image.tar.xz",
            env!("WORKSPACE_ROOT")
        )
        .into();
        let container_bundle = format!(
            "{}oak_containers_hello_world_container/target/oak_container_example_oci_filesystem_bundle.tar",
            env!("WORKSPACE_ROOT")
        ).into();
        Self {
            system_image,
            container_bundle,
            application_config: None,
            qemu_params: qemu::Params::default_for_test(),
        }
    }
}

pub fn path_exists(s: &str) -> Result<std::path::PathBuf, String> {
    let path = std::path::PathBuf::from(s);
    if !std::fs::metadata(s)
        .map_err(|err| err.to_string())?
        .is_file()
    {
        Err(String::from("path does not represent a file"))
    } else {
        Ok(path)
    }
}

pub struct Launcher {
    vmm: qemu::Qemu,
    server: JoinHandle<Result<(), anyhow::Error>>,
    host_proxy_port: u16,
    attestation_endorsement: AttestationEndorsement,
    // Endorsed Attestation Evidence consists of Attestation Evidence (initialized by the
    // Orchestrator) and Attestation Endorsement (initialized by the Launcher).
    endorsed_attestation_evidence: Option<AttestationBundle>,
    // Receiver that is used to get the Attestation Evidence from the server implementation.
    attestation_evidence_receiver: Option<Receiver<AttestationEvidence>>,
    app_ready_notifier: Option<Receiver<()>>,
    trusted_app_address: Option<SocketAddr>,
    shutdown: Option<Sender<()>>,
}

impl Launcher {
    pub async fn create(args: Args) -> Result<Self, anyhow::Error> {
        // Let the OS assign an open port for the launcher service.
        let sockaddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
        let listener = TcpListener::bind(sockaddr).await?;
        let port = listener.local_addr()?.port();
        log::info!("Launcher service listening on port {port}");
        let (attestation_evidence_sender, attestation_evidence_receiver) =
            channel::<AttestationEvidence>();
        let (shutdown_sender, shutdown_receiver) = channel::<()>();
        let (app_notifier_sender, app_notifier_receiver) = channel::<()>();
        let server = tokio::spawn(server::new(
            listener,
            args.system_image,
            args.container_bundle,
            args.application_config,
            attestation_evidence_sender,
            app_notifier_sender,
            shutdown_receiver,
        ));

        // Also get an open port for that QEMU can use for proxying requests to the server. Since we
        // don't have a mechanism to pass this port to QEMU we have to unbind it by dropping it.
        // There is a small window for a race condition, but since the assigned port will be random
        // the probability of another process grabbing the port before QEMU can should be very low.
        let host_proxy_port = { TcpListener::bind(sockaddr).await?.local_addr()?.port() };
        let vmm = qemu::Qemu::start(args.qemu_params, port, host_proxy_port)?;

        Ok(Self {
            vmm,
            server,
            host_proxy_port,
            // TODO(#3640): Provide hardware manufacturer's certificates.
            attestation_endorsement: AttestationEndorsement {
                tee_certificates: vec![],
                application_data: None,
            },
            // Attestation Evidence will be sent by the Orchestrator once generated.
            // And after the Evidence is received it will be endorsed by the Launcher (it will
            // provide corresponding hardware manufacturer's certificates).
            endorsed_attestation_evidence: None,
            attestation_evidence_receiver: Some(attestation_evidence_receiver),
            app_ready_notifier: Some(app_notifier_receiver),
            trusted_app_address: None,
            shutdown: Some(shutdown_sender),
        })
    }

    /// Gets the address that the untrusted application can use to connect to the trusted
    /// application.
    ///
    /// This is a host-visible address that the VMM will proxy to the trusted application's service
    /// endpoint.
    ///
    /// This call will wait until the trusted app has notifiied the launcher once that it is ready
    /// via the orchestrator.
    pub async fn get_trusted_app_address(&mut self) -> Result<SocketAddr, anyhow::Error> {
        // If we haven't received a ready notification, wait for it.
        if let Some(receiver) = self.app_ready_notifier.take() {
            // Set a timeout since we don't want to wait forever if the VM didn't start properly.
            timeout(Duration::from_secs(VM_START_TIMEOUT), receiver).await??;
            self.trusted_app_address.replace(SocketAddr::new(
                IpAddr::V4(PROXY_ADDRESS),
                self.host_proxy_port,
            ));
        }
        self.trusted_app_address
            .ok_or_else(|| anyhow::anyhow!("trusted app address not set"))
    }

    /// Gets the endorsed attestation evidence that the untrusted application can send to remote
    /// clients, which will verify it before connecting.
    pub async fn get_endorsed_evidence(&mut self) -> anyhow::Result<AttestationBundle> {
        // If we haven't received an attestation evidence, wait for it.
        #[allow(deprecated)]
        if let Some(receiver) = self.attestation_evidence_receiver.take() {
            // Set a timeout since we don't want to wait forever if the VM didn't start properly.
            let evidence = timeout(Duration::from_secs(VM_START_TIMEOUT), receiver)
                .await
                .context("couldn't get attestation evidence before timeout")?
                .context("no attestation evidence available")?;
            #[allow(deprecated)]
            let endorsed_attestation_evidence = AttestationBundle {
                attestation_evidence: Some(evidence),
                attestation_endorsement: Some(self.attestation_endorsement.clone()),
                dice_evidence: None,
            };
            self.endorsed_attestation_evidence
                .replace(endorsed_attestation_evidence);
        }
        self.endorsed_attestation_evidence
            .clone()
            .ok_or_else(|| anyhow::anyhow!("endorsed evidence is not set"))
    }

    pub async fn wait(&mut self) -> Result<(), anyhow::Error> {
        self.vmm.wait().await?;
        Ok(())
    }

    pub async fn kill(&mut self) {
        if let Some(shutdown) = self.shutdown.take() {
            let _ = shutdown.send(());
        }
        let _ = self.vmm.kill().await;
        self.server.abort();
    }
}
