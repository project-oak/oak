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

use crate::vmm::{Params, Vmm};
use anyhow::Result;
use async_trait::async_trait;
use command_fds::tokio::CommandFdAsyncExt;
use log::info;
use std::{
    net::Shutdown,
    os::unix::{
        io::{AsRawFd, OwnedFd},
        net::UnixStream,
    },
    process::Stdio,
};

pub struct Crosvm {
    console: UnixStream,
    instance: tokio::process::Child,
}

impl Crosvm {
    pub fn start(params: Params) -> Result<Self> {
        let mut cmd = tokio::process::Command::new(params.binary);

        cmd.stdin(OwnedFd::from(params.comms.try_clone()?));
        cmd.stdout(OwnedFd::from(params.comms));
        cmd.stderr(Stdio::inherit());
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
        cmd.arg("--serial=num=2,hardware=serial,type=stdout,stdin");
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
}
