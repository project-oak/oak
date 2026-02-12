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

mod noise;
mod tls;

use std::{net::SocketAddr, sync::Arc};

use anyhow::Context;
use clap::Parser;
use oak_proxy_lib::config::{RestartPolicy, ServerConfig};
use tokio::{net::TcpListener, process::Command};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the TOML configuration file.
    #[arg(long, value_parser = oak_proxy_lib::config::load_toml::<ServerConfig>)]
    config: ServerConfig,

    /// The SocketAddr where the proxy should listen for client connections
    /// (e.g., "0.0.0.0:8080"). This will override the value in the config
    /// file.
    #[arg(long, env = "OAK_PROXY_SERVER_LISTEN_ADDRESS")]
    listen_address: Option<SocketAddr>,

    /// Address of the backend application.
    #[arg(long, env = "OAK_PROXY_SERVER_BACKEND_ADDRESS")]
    backend_address: Option<SocketAddr>,
}

impl Args {
    fn get_config(mut self) -> anyhow::Result<ServerConfig> {
        // The command-line arguments override the values from the config file.
        if let Some(listen_address) = self.listen_address {
            self.config.listen_address = Some(listen_address);
        }
        if let Some(backend_address) = self.backend_address {
            self.config.backend_address = Some(backend_address);
        }

        self.config
            .listen_address
            .as_ref()
            .context("listen_address must be specified in the config file or via an argument")?;
        self.config
            .backend_address
            .as_ref()
            .context("backend_address must be specified in the config file or via an argument")?;

        Ok(self.config)
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();

    let config = Arc::new(Args::parse().get_config()?);

    if config.backend_command.is_some() {
        tokio::spawn(backend_task(config.clone()));
    }

    let listen_address = config.listen_address.unwrap();
    let listener = TcpListener::bind(listen_address).await?;
    log::info!("[Server] Listening on {}", listen_address);

    if config.experimental_tls_session {
        tls::run_loop(listener, config).await
    } else {
        noise::run_loop(listener, config).await
    }
}

async fn backend_task(config: Arc<ServerConfig>) {
    let backend_command = config.backend_command.as_ref().unwrap(); // Some by construction
    log::info!(
        "Starting backend command: {} with args {:?}",
        backend_command.cmd,
        backend_command.args
    );

    loop {
        let mut cmd = Command::new(&backend_command.cmd);
        cmd.args(&backend_command.args);
        let mut child = match cmd.spawn() {
            Ok(child) => child,
            Err(err) => {
                log::error!("Failed to start backend command: {:?}", err);
                std::process::exit(1);
            }
        };

        let status: Result<std::process::ExitStatus, std::io::Error> = child.wait().await;
        log::warn!("Backend process exited with status: {:?}", status);
        match backend_command.restart_policy {
            RestartPolicy::Always => {
                log::info!("Restarting backend process...");
            }
            RestartPolicy::Never => {
                log::warn!("Backend process exited and restart policy is Never");
            }
            RestartPolicy::Terminate => {
                log::error!("Backend process exited and restart policy is Terminate");
                std::process::exit(1);
            }
        }
    }
}
