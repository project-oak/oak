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
use log::info;
use std::{
    net::Shutdown,
    os::unix::{io::AsRawFd, net::UnixStream},
    path::PathBuf,
    process::Stdio,
};

/// Parameters used for launching VM instances
#[derive(Parser, Clone, Debug, PartialEq)]
pub struct Params {
    /// Path to the VMM binary to execute.
    #[arg(long, value_parser = path_exists)]
    pub vmm_binary: PathBuf,

    /// Path to the enclave binary to load into the VM.
    #[arg(long, value_parser = path_exists)]
    pub enclave_binary: PathBuf,

    /// Path to the BIOS image to use.
    #[arg(long, value_parser = path_exists)]
    pub bios_binary: PathBuf,

    /// Port to use for debugging with gdb
    #[arg(long = "gdb")]
    pub gdb: Option<u16>,
}

pub struct Instance {
    console: UnixStream,
    comms: UnixStream,
    instance: tokio::process::Child,
}

impl Instance {
    pub fn start(params: Params, console: UnixStream) -> Result<Self> {
        let mut cmd = tokio::process::Command::new(params.vmm_binary);

        let (comms_guest, comms_host) = UnixStream::pair()?;

        cmd.stderr(Stdio::inherit());
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::inherit());
        cmd.preserved_fds(vec![console.as_raw_fd(), comms_guest.as_raw_fd()]);

        // Needed to expose advanced CPU features. Specifically RDRAND which is required for remote
        // attestation.
        cmd.arg("-enable-kvm");
        cmd.args(&["-cpu", "IvyBridge-IBRS,enforce"]);

        // Disable a bunch of hardware we don't need.
        cmd.arg("-nodefaults");
        cmd.arg("-nographic");
        // If the VM restarts, don't restart it (we're not expecting any restarts so any restart
        // should be treated as a failure)
        cmd.arg("-no-reboot");
        // Use the `microvm` machine as the basis, and enable PCIe as we need vhost-vsock-pci.
        cmd.args(["-machine", "microvm,pcie=on"]);
        // Route first serial port to console.
        cmd.args(&[
            "-chardev",
            format!("socket,id=consock,fd={}", console.as_raw_fd()).as_str(),
        ]);
        cmd.args(["-serial", "chardev:consock"]);
        // Add the vsock device.
        cmd.args([
            "-chardev",
            format!("socket,id=commsock,fd={}", comms_guest.as_raw_fd()).as_str(),
        ]);
        cmd.args(["-device", "virtio-serial-device,max_ports=1"]);
        cmd.args(["-device", "virtconsole,chardev=commsock"]);
        // Load the kernel ELF via the loader device.
        cmd.args([
            "-device",
            format!("loader,file={}", params.enclave_binary.display()).as_str(),
        ]);
        cmd.args([
            "-bios",
            params
                .bios_binary
                .into_os_string()
                .into_string()
                .unwrap()
                .as_str(),
        ]);
        // Leaving it here for postieriority, as currently stage0 doesn't set up the command line.
        cmd.args(["-fw_cfg", "name=cmdline_data,string=channel=virtio_vsock"]);

        if let Some(gdb_port) = params.gdb {
            // Listen for a gdb connection on the provided port and wait for debugger before booting
            cmd.args(["-gdb", format!("tcp::{}", gdb_port).as_str()]);
            cmd.arg("-S");
        }

        info!("Executing: {:?}", cmd);

        Ok(Self {
            instance: cmd.spawn()?,
            comms: comms_host,
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

    async fn create_comms_channel(&self) -> Result<Box<dyn oak_channel::Channel>> {
        Ok(Box::new(self.comms.try_clone()?))
    }
}
