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
use log::info;
use std::{
    io::{Error, ErrorKind, Read, Write},
    net::Shutdown,
    os::unix::{io::AsRawFd, net::UnixStream},
    process::Stdio,
};
use vsock::VsockStream;

/// The guest VM context ID for virtio vsock connecitons.
const VSOCK_GUEST_CID: u32 = 3;

/// The guest VM virtio vsock port.
const VSOCK_GUEST_PORT: u32 = 1024;

pub struct Crosvm {
    console: UnixStream,
    instance: tokio::process::Child,
}

/// A wrapper for a vsock stream that can be used as a communication channel between the loader and
/// the guest VM.
///
/// The vsock channel can only be created after the VM is booted, so we start without a stream and
/// only connect later when we try to use it for the first time.
pub struct VsockStreamChannel {
    stream: Option<VsockStream>,
}

impl VsockStreamChannel {
    /// Ensures that the inner stream is connected to the VM.
    fn ensure_stream(&mut self) -> std::io::Result<()> {
        if self.stream.is_none() {
            let stream = VsockStream::connect_with_cid_port(VSOCK_GUEST_CID, VSOCK_GUEST_PORT)?;
            self.stream.replace(stream);
        }
        Ok(())
    }
}

impl Write for VsockStreamChannel {
    fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
        self.ensure_stream()?;
        self.stream
            .as_mut()
            .ok_or_else(|| Error::from(ErrorKind::NotConnected))?
            .write(data)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.ensure_stream()?;
        self.stream
            .as_mut()
            .ok_or_else(|| Error::from(ErrorKind::NotConnected))?
            .flush()
    }
}

impl Read for VsockStreamChannel {
    fn read(&mut self, data: &mut [u8]) -> std::io::Result<usize> {
        self.ensure_stream()?;
        self.stream
            .as_mut()
            .ok_or_else(|| Error::from(ErrorKind::NotConnected))?
            .read(data)
    }
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

    fn create_comms_channel(&self) -> Result<Box<dyn ReadWrite>> {
        Ok(Box::new(VsockStreamChannel { stream: None }))
    }
}
