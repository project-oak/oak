//
// Copyright 2022 The Project Oak Authors
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

use crate::{instance::LaunchedInstance, path_exists};
use anyhow::Result;
use async_trait::async_trait;
use clap::Parser;
use command_fds::tokio::CommandFdAsyncExt;
use futures::TryFutureExt;
use log::info;
use std::{
    net::Shutdown,
    os::unix::{io::AsRawFd, net::UnixStream},
    path::PathBuf,
    process::Stdio,
};
use tokio::time::{sleep, timeout, Duration};
use vsock::VsockStream;

// The guest VM context ID for virtio vsock connections.
const VSOCK_GUEST_CID: u32 = 3;

// The guest VM virtio vsock port.
const VSOCK_GUEST_PORT: u32 = 1024;

/// Parameters used for launching VM instances
#[derive(Parser, Clone, Debug, PartialEq)]
pub struct Params {
    /// Path to the VMM binary to execute.
    #[clap(long, parse(from_os_str), validator = path_exists)]
    pub vmm_binary: PathBuf,

    /// Path to the binary to load into the VM.
    #[clap(long, parse(from_os_str), validator = path_exists)]
    pub app_binary: PathBuf,

    /// Port to use for debugging with gdb
    #[clap(long = "gdb")]
    pub gdb: Option<u16>,
}

pub struct Instance {
    console: UnixStream,
    instance: tokio::process::Child,
}

impl Instance {
    pub fn start(params: Params, console: UnixStream) -> Result<Self> {
        let mut cmd = tokio::process::Command::new(params.vmm_binary);

        cmd.stderr(Stdio::inherit());
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::inherit());
        cmd.preserved_fds(vec![console.as_raw_fd()]);

        // Construct the command-line arguments for `crosvm`.
        cmd.arg("run");
        // Don't bother running devices in sandboxed processes.
        cmd.arg("--disable-sandbox");
        // First serial port: this will be used by the console
        cmd.args(&[
            "--serial",
            format!(
                "num=1,hardware=serial,type=file,path=/proc/self/fd/{},console,earlycon",
                console.as_raw_fd()
            )
            .as_str(),
        ]);
        cmd.args(["--cid", VSOCK_GUEST_CID.to_string().as_str()]);
        cmd.args(["--params", "channel=virtio_vsock"]);

        if let Some(gdb_port) = params.gdb {
            // Listen for a gdb connection on the provided port and wait for debugger before booting
            cmd.args(&["--gdb", format!("{}", gdb_port).as_str()]);
        }

        cmd.arg(params.app_binary);

        info!("Executing: {:?}", cmd);

        Ok(Self {
            instance: cmd.spawn()?,
            console,
        })
    }
}

#[async_trait]
impl LaunchedInstance for Instance {
    async fn wait(&mut self) -> Result<std::process::ExitStatus> {
        self.instance.wait().await.map_err(anyhow::Error::from)
    }

    async fn kill(mut self: Box<Self>) -> Result<std::process::ExitStatus> {
        info!("Cleaning up and shutting down.");
        self.console.shutdown(Shutdown::Both)?;
        self.instance.start_kill()?;
        self.wait().await
    }

    async fn create_comms_channel(
        &self,
    ) -> Result<Box<dyn oak_baremetal_communication_channel::Channel>> {
        // The vsock channel can only be created after the VM is booted. Hence
        // we try a few times to connect, in case the VM is currently starting
        // up. If no connetion is established after a while, we timeout.
        let task = tokio::spawn(async {
            let stream: Box<dyn oak_baremetal_communication_channel::Channel> = loop {
                match VsockStream::connect_with_cid_port(VSOCK_GUEST_CID, VSOCK_GUEST_PORT) {
                    Ok(stream) => {
                        break Box::new(stream);
                    }
                    Err(_error) => {
                        sleep(Duration::from_millis(100)).await;
                        continue;
                    }
                }
            };
            stream
        })
        .map_err(anyhow::Error::msg);
        timeout(Duration::from_millis(1000), task).await?
    }
}
