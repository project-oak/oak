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

use crate::{
    vmm::{Params, Vmm},
    ReadWrite,
};
use anyhow::Result;
use async_trait::async_trait;
use command_fds::tokio::CommandFdAsyncExt;
use futures::TryFutureExt;
use log::info;
use std::{
    net::Shutdown,
    os::unix::{io::AsRawFd, net::UnixStream},
    process::Stdio,
};
use tokio::time::{sleep, timeout, Duration};
use vsock::VsockStream;

// The guest VM context ID for virtio vsock connections.
const VSOCK_GUEST_CID: u32 = 3;

// The guest VM virtio vsock port.
const VSOCK_GUEST_PORT: u32 = 1024;

pub struct Crosvm {
    console: UnixStream,
    instance: tokio::process::Child,
}

impl Crosvm {
    pub fn start(params: Params) -> Result<Self> {
        let mut cmd = tokio::process::Command::new(params.binary);

        cmd.stderr(Stdio::inherit());
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::inherit());
        cmd.preserved_fds(vec![params.console.as_raw_fd()]);

        // Construct the command-line arguments for `crosvm`.
        cmd.arg("run");
        // Don't bother running devices in sandboxed processes.
        cmd.arg("--disable-sandbox");
        // First serial port: this will be used by the console
        cmd.arg(format!(
            "--serial=num=1,hardware=serial,type=file,path=/proc/self/fd/{},console,earlycon",
            params.console.as_raw_fd()
        ));
        cmd.arg(format!("--cid={}", VSOCK_GUEST_CID));
        cmd.arg(params.app);

        info!("Executing: {:?}", cmd);

        Ok(Crosvm {
            instance: cmd.spawn()?,
            console: params.console,
        })
    }
}

#[async_trait]
impl Vmm for Crosvm {
    async fn wait(&mut self) -> Result<std::process::ExitStatus> {
        self.instance.wait().await.map_err(anyhow::Error::from)
    }

    async fn kill(mut self: Box<Self>) -> Result<std::process::ExitStatus> {
        info!("Cleaning up and shutting down.");
        self.console.shutdown(Shutdown::Both)?;
        self.instance.start_kill()?;
        self.wait().await
    }

    async fn create_comms_channel(&self) -> Result<Box<dyn ReadWrite>> {
        // The vsock channel can only be created after the VM is booted. Hence
        // we try a few times to connect, in case the VM is currently starting
        // up. If no connetion is established after a while, we timeout.
        let task = tokio::spawn(async {
            let stream: Box<dyn ReadWrite> = loop {
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
        timeout(Duration::from_millis(10 * 1000), task).await?
    }
}
