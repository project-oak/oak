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

use crate::{instance::LaunchedInstance, NativeParams};
use anyhow::Result;
use async_trait::async_trait;
use command_fds::tokio::CommandFdAsyncExt;
use log::info;
use std::{
    net::Shutdown,
    os::unix::{io::AsRawFd, net::UnixStream},
};

/// An instance of the runtime running directly as a linux binary
pub struct NativeInstance {
    comms_host: UnixStream,
    instance: tokio::process::Child,
}

impl NativeInstance {
    pub fn start(params: NativeParams) -> Result<Self> {
        let (comms_guest, comms_host) = UnixStream::pair()?;

        let mut cmd = tokio::process::Command::new(params.app_binary);

        // Print any logs & errors
        cmd.stdout(std::process::Stdio::inherit());
        cmd.stderr(std::process::Stdio::inherit());

        cmd.preserved_fds(vec![comms_guest.as_raw_fd()]);
        cmd.args(&["--comms-fd", &comms_guest.as_raw_fd().to_string()]);

        let instance = cmd.spawn()?;

        Ok(Self {
            instance,
            comms_host,
        })
    }
}

#[async_trait]
impl LaunchedInstance for NativeInstance {
    async fn wait(&mut self) -> Result<std::process::ExitStatus> {
        self.instance.wait().await.map_err(anyhow::Error::from)
    }

    async fn kill(mut self: Box<Self>) -> Result<std::process::ExitStatus> {
        info!("Cleaning up and shutting down.");
        self.comms_host.shutdown(Shutdown::Both)?;
        self.instance.start_kill()?;
        self.wait().await
    }

    async fn create_comms_channel(
        &self,
    ) -> Result<Box<dyn oak_baremetal_communication_channel::Channel>> {
        let comms_host = self.comms_host.try_clone()?;
        Ok(Box::new(comms_host))
    }
}
