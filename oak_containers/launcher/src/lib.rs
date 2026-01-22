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

#![feature(let_chains)]

mod qemu;
mod server;

use std::{
    fmt::Display,
    net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr},
};

use anyhow::Context;
use clap::{Parser, ValueEnum};
use oak_grpc::oak::key_provisioning::v1::key_provisioning_client::KeyProvisioningClient;
use oak_proto_rust::oak::{
    attestation::v1::{endorsements, Endorsements, Evidence, OakContainersEndorsements},
    key_provisioning::v1::{GetGroupKeysRequest, GetGroupKeysResponse},
    session::v1::EndorsedEvidence,
};
pub use qemu::{Params as QemuParams, VmType as QemuVmType};
use tokio::{
    net::TcpListener,
    sync::{oneshot, watch},
    task::JoinHandle,
    time::{timeout, Duration},
};
use tokio_vsock::{VsockAddr, VsockListener, VMADDR_CID_HOST};
use tonic::transport::Channel as TonicChannel;

/// IP address for the host on the virtual network.
const VM_HOST_ADDRESS: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 2, 100));

/// IPv6 address for the host on the virtual network.
// We use a Unique Local Address from the fd00::/8 block, with a random global
// id.
//
// Global id = d2:a994:f3c5, subnet = 0001, interface id = 10:0:2:64
// (so that the addresses match the IPv4 ones for ease of understanding)
#[allow(unused)]
const VM_HOST_ADDRESS_6: IpAddr =
    IpAddr::V6(Ipv6Addr::new(0xFDD2, 0xA994, 0xF3C5, 0x0001, 0x0010, 0x0000, 0x0002, 0x00064));

/// Port where the launcher will listen on the virtual network.
const VM_HOST_PORT: u16 = 8080;

/// The local IP address assigned to the VM guest.
const VM_LOCAL_ADDRESS: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 2, 15));

/// The local IPv6 address assigned to the VM guest.
const VM_LOCAL_ADDRESS_6: IpAddr =
    IpAddr::V6(Ipv6Addr::new(0xFDD2, 0xA994, 0xF3C5, 0x0001, 0x0010, 0x0000, 0x0002, 0x00015));

/// The local port that the VM guest should be listening on.
const VM_LOCAL_PORT: u16 = 8080;

/// The local port that the Orchestrator should be listening on.
const VM_ORCHESTRATOR_LOCAL_PORT: u16 = 4000;

/// The local address that will be forwarded by the VMM to the guest's IP
/// adress.
const PROXY_ADDRESS: Ipv4Addr = Ipv4Addr::LOCALHOST;

/// Number of seconds to wait for the VM to start up.
const VM_START_TIMEOUT: u64 = 300;

#[derive(Clone, Debug, Default, Eq, PartialEq, ValueEnum)]
pub enum ChannelType {
    /// Use virtual networking.
    #[default]
    Network,

    /// Use TUN/TAP networking; assumes there is a `oak0` TAP device configured.
    Tap,

    // Use virtio-vsock.
    VirtioVsock,
}

#[derive(Parser, Debug)]
#[group(skip)]
pub struct Args {
    #[arg(long, required = true, value_parser = path_exists,)]
    pub system_image: std::path::PathBuf,
    #[arg(long, required = true, value_parser = path_exists,)]
    pub container_bundle: std::path::PathBuf,
    #[clap(skip)]
    pub application_config: Vec<u8>,
    #[command(flatten)]
    pub qemu_params: qemu::Params,

    // Method of communication with the trusted application in the enclave.
    #[arg(long, value_enum, default_value_t = ChannelType::default())]
    pub communication_channel: ChannelType,
}

pub fn path_exists(s: &str) -> Result<std::path::PathBuf, String> {
    let path = std::path::PathBuf::from(s);
    if !std::fs::metadata(s).map_err(|err| err.to_string())?.is_file() {
        Err(String::from("path does not represent a file"))
    } else {
        Ok(path)
    }
}

#[derive(Clone)]
pub enum Channel {
    Network { host_proxy_port: u16, trusted_app_address: Option<SocketAddr> },
    Tap,
    VirtioVsock { trusted_app_address: Option<VsockAddr> },
}

/// Interface that is connected to the trusted application.
pub enum TrustedApplicationAddress {
    Network(SocketAddr),
    VirtioVsock(VsockAddr),
}

impl TryFrom<Channel> for TrustedApplicationAddress {
    type Error = anyhow::Error;

    fn try_from(channel: Channel) -> Result<TrustedApplicationAddress, Self::Error> {
        match channel {
            Channel::Network { host_proxy_port: _, trusted_app_address } => {
                trusted_app_address.map(TrustedApplicationAddress::Network)
            }
            Channel::Tap => Some(TrustedApplicationAddress::Network(SocketAddr::new(
                VM_LOCAL_ADDRESS,
                VM_LOCAL_PORT,
            ))),
            Channel::VirtioVsock { trusted_app_address } => {
                trusted_app_address.map(TrustedApplicationAddress::VirtioVsock)
            }
        }
        .ok_or_else(|| anyhow::anyhow!("trusted application address not set"))
    }
}

impl Display for TrustedApplicationAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TrustedApplicationAddress::Network(addr) => addr.fmt(f),
            TrustedApplicationAddress::VirtioVsock(addr) => addr.fmt(f),
        }
    }
}

pub struct Launcher {
    vmm: qemu::Qemu,
    server: JoinHandle<Result<(), anyhow::Error>>,
    host_orchestrator_proxy_port: u16,
    // Endorsed Attestation Evidence consists of Attestation Evidence (initialized by the
    // Orchestrator) and Attestation Endorsement (initialized by the Launcher).
    endorsed_evidence: Option<EndorsedEvidence>,
    // Receiver that is used to get the Attestation Evidence from the server implementation.
    evidence_receiver: Option<oneshot::Receiver<Evidence>>,
    app_ready_notifier: Option<oneshot::Receiver<()>>,
    orchestrator_key_provisioning_client: Option<KeyProvisioningClient<TonicChannel>>,
    trusted_app_channel: Channel,
    shutdown: Option<watch::Sender<()>>,
}

impl Launcher {
    pub async fn create(args: Args) -> Result<Self, anyhow::Error> {
        // Let the OS assign an open port for the launcher service.
        let sockaddr = match args.communication_channel {
            ChannelType::Network | ChannelType::VirtioVsock => {
                SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0)
            }
            ChannelType::Tap => SocketAddr::new(VM_HOST_ADDRESS, VM_HOST_PORT),
        };
        let orchestrator_sockaddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
        let listener = TcpListener::bind(sockaddr).await?;
        let port = listener.local_addr()?.port();

        // Reuse the same port we got for the TCP socket for vsock.
        let vsock_listener = VsockListener::bind(VsockAddr::new(VMADDR_CID_HOST, port.into()))
            .expect("Bind failed. Check if kernel mod vhost_vsock is loaded. Try running `sudo modprobe vhost_vsock` to load it.");
        log::info!("Launcher service listening on port {port}");
        let (evidence_sender, evidence_receiver) = oneshot::channel::<Evidence>();
        let (shutdown_sender, mut shutdown_receiver) = watch::channel::<()>(());
        shutdown_receiver.mark_unchanged(); // Don't immediately notify on the initial value.
        let (app_notifier_sender, app_notifier_receiver) = oneshot::channel::<()>();
        let endorsements = get_endorsements();
        let server = tokio::spawn(server::new(
            listener,
            vsock_listener,
            args.system_image,
            args.container_bundle,
            args.application_config,
            evidence_sender,
            app_notifier_sender,
            shutdown_receiver,
            endorsements,
        ));

        let trusted_app_channel = match args.communication_channel {
            ChannelType::Network => {
                // Also get an open port for that QEMU can use for proxying requests to the
                // server. Since we don't have a mechanism to pass this port to
                // QEMU we have to unbind it by dropping it. There is a small
                // window for a race condition, but since the assigned port will
                // be random the probability of another process grabbing the
                // port before QEMU can should be very low.
                let host_proxy_port = TcpListener::bind(sockaddr).await?.local_addr()?.port();
                Channel::Network { host_proxy_port, trusted_app_address: None }
            }
            ChannelType::Tap => Channel::Tap,
            ChannelType::VirtioVsock => Channel::VirtioVsock { trusted_app_address: None },
        };

        let host_orchestrator_proxy_port =
            { TcpListener::bind(orchestrator_sockaddr).await?.local_addr()?.port() };
        let vmm = qemu::Qemu::start(
            args.qemu_params,
            match trusted_app_channel {
                Channel::Network { host_proxy_port, trusted_app_address: _ } => {
                    qemu::Network::Proxy {
                        launcher_service_port: port,
                        host_proxy_port: Some(host_proxy_port),
                        host_orchestrator_proxy_port,
                    }
                }
                Channel::Tap => qemu::Network::Tap,
                Channel::VirtioVsock { trusted_app_address: _ } => qemu::Network::Proxy {
                    launcher_service_port: port,
                    host_proxy_port: None,
                    host_orchestrator_proxy_port,
                },
            },
        )?;

        Ok(Self {
            vmm,
            server,
            host_orchestrator_proxy_port,
            // Attestation Evidence will be sent by the Orchestrator once generated.
            // And after the Evidence is received it will be endorsed by the Launcher (it will
            // provide corresponding hardware manufacturer's certificates).
            endorsed_evidence: None,
            evidence_receiver: Some(evidence_receiver),
            app_ready_notifier: Some(app_notifier_receiver),
            orchestrator_key_provisioning_client: None,
            trusted_app_channel,
            shutdown: Some(shutdown_sender),
        })
    }

    /// Gets the address that the untrusted application can use to connect to
    /// the trusted application.
    ///
    /// This is a host-visible address that the VMM will proxy to the trusted
    /// application's service endpoint.
    ///
    /// This call will wait until the trusted app has notifiied the launcher
    /// once that it is ready via the orchestrator.
    pub async fn get_trusted_app_address(
        &mut self,
    ) -> Result<TrustedApplicationAddress, anyhow::Error> {
        // If we haven't received a ready notification, wait for it.
        if let Some(receiver) = self.app_ready_notifier.take() {
            // Set a timeout since we don't want to wait forever if the VM didn't start
            // properly.
            timeout(Duration::from_secs(VM_START_TIMEOUT), receiver).await??;
            match &mut self.trusted_app_channel {
                Channel::Network { host_proxy_port, trusted_app_address } => {
                    trusted_app_address
                        .replace(SocketAddr::new(IpAddr::V4(PROXY_ADDRESS), *host_proxy_port));
                }
                Channel::Tap => {}
                Channel::VirtioVsock { trusted_app_address } => {
                    trusted_app_address.replace(VsockAddr::new(
                        self.vmm.guest_cid().expect("VMM does not have a guest CID"),
                        VM_LOCAL_PORT.into(),
                    ));
                }
            }
        }
        self.trusted_app_channel.clone().try_into()
    }

    /// Gets the endorsed attestation evidence that the untrusted application
    /// can send to remote clients, which will verify it before connecting.
    pub async fn get_endorsed_evidence(&mut self) -> anyhow::Result<EndorsedEvidence> {
        // If we haven't received an attestation evidence, wait for it.
        #[allow(deprecated)]
        if let Some(receiver) = self.evidence_receiver.take() {
            // Set a timeout since we don't want to wait forever if the VM didn't start
            // properly.
            let evidence = timeout(Duration::from_secs(VM_START_TIMEOUT), receiver)
                .await
                .context("couldn't get attestation evidence before timeout")?
                .context("no attestation evidence available")?;

            let endorsements = get_endorsements();

            let endorsed_evidence =
                EndorsedEvidence { evidence: Some(evidence), endorsements: Some(endorsements) };
            self.endorsed_evidence.replace(endorsed_evidence);
        }
        self.endorsed_evidence
            .clone()
            .ok_or_else(|| anyhow::anyhow!("endorsed evidence is not set"))
    }

    // Gets enclave group keys as part of Key Provisioning.
    pub async fn get_group_keys(
        &mut self,
        request: GetGroupKeysRequest,
    ) -> anyhow::Result<GetGroupKeysResponse> {
        if self.orchestrator_key_provisioning_client.is_none() {
            // Create Orchestrator Key Provisioning gRPC client.
            let orchestrator_uri =
                format!("http://127.0.0.1:{}", self.host_orchestrator_proxy_port)
                    .parse()
                    .context("couldn't parse orchestrator URI")?;
            let orchestrator_channel = TonicChannel::builder(orchestrator_uri)
                .connect()
                .await
                .context("couldn't connect to orchestrator")?;
            self.orchestrator_key_provisioning_client =
                Some(KeyProvisioningClient::new(orchestrator_channel));
        }

        let get_group_keys_response = self
            .orchestrator_key_provisioning_client
            .clone()
            .context("couldn't get orchestrator key provisioning client")?
            .get_group_keys(request)
            .await
            .context("couldn't get group keys")?
            .into_inner();
        Ok(get_group_keys_response)
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

fn get_endorsements() -> Endorsements {
    Endorsements {
        r#type: Some(endorsements::Type::OakContainers(OakContainersEndorsements {
            root_layer: None,
            kernel_layer: None,
            system_layer: None,
            container_layer: None,
        })),
        // TODO: b/375137648 - Populate `events` proto field.
        ..Default::default()
    }
}
