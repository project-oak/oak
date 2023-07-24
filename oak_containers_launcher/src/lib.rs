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

mod qemu;
mod server;

use clap::Parser;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use tokio::{
    sync::oneshot::{channel, Receiver, Sender},
    task::JoinHandle,
};

/// The local IP address assigned to the VM guest.
const VM_LOCAL_ADDRESS: IpAddr = IpAddr::V4(Ipv4Addr::new(10, 0, 2, 15));

/// The local port that the VM guest should be listening on.
const VM_LOCAL_PORT: u16 = 8080;

#[derive(Parser, Debug)]
pub struct Args {
    #[arg(long, default_value_t = 8080)]
    port: u16,
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
            port: 8080,
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
    app_ready_notifier: Option<Receiver<SocketAddr>>,
    trusted_app_address: Option<SocketAddr>,
    shutdown: Option<Sender<()>>,
}

impl Launcher {
    pub async fn create(args: Args) -> Result<Self, anyhow::Error> {
        let sockaddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), args.port);
        let (shutdown_sender, shutdown_receiver) = channel::<()>();
        let (app_notifier_sender, app_notifier_receiver) = channel::<SocketAddr>();
        let server = tokio::spawn(server::new(
            sockaddr,
            args.system_image,
            args.container_bundle,
            args.application_config,
            app_notifier_sender,
            shutdown_receiver,
        ));

        let vmm = qemu::Qemu::start(args.qemu_params)?;

        Ok(Self {
            vmm,
            server,
            app_ready_notifier: Some(app_notifier_receiver),
            trusted_app_address: None,
            shutdown: Some(shutdown_sender),
        })
    }

    /// Gets the address on which the trusted app is listening.
    ///
    /// This call will wait until the trusted app has notifiied the launcher once that it is ready
    /// via the orchestrator.
    pub async fn get_trusted_app_address(&mut self) -> Result<SocketAddr, anyhow::Error> {
        // If we haven't received a ready notification, wait for it.
        if let Some(receiver) = self.app_ready_notifier.take() {
            // Set a timeout of 30 seconds, since we don't want to wait forever if the VM didn't
            // start properly.
            let sleep = tokio::time::sleep(tokio::time::Duration::from_secs(30));

            tokio::select! {
                result = receiver => {
                    self.trusted_app_address.replace(result?);
                }
                _ = sleep => {}
            }
        }
        self.trusted_app_address
            .ok_or_else(|| anyhow::anyhow!("trusted app address not set"))
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
