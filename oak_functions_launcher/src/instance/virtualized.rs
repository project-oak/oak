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

use crate::instance::LaunchedInstance;
use anyhow::{Context, Result};
use async_trait::async_trait;
use clap::Parser;
use command_fds::tokio::CommandFdAsyncExt;
use log::info;
use oak_channel::{Channel, Write};
use std::{
    fs,
    net::Shutdown,
    os::unix::{io::AsRawFd, net::UnixStream},
    path::PathBuf,
    process::Stdio,
};

fn path_exists(s: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(s);
    if !fs::metadata(s).map_err(|err| err.to_string())?.is_file() {
        Err(String::from("path does not represent a file"))
    } else {
        Ok(path)
    }
}

const PAGE_SIZE: usize = 4096;

/// Parameters used for launching VM instances
#[derive(Parser, Clone, Debug, PartialEq)]
pub struct Params {
    /// Path to the VMM binary to execute.
    #[arg(long, value_parser = path_exists)]
    pub vmm_binary: PathBuf,

    /// Path to the enclave binary to load into the VM.
    #[arg(long, value_parser = path_exists)]
    pub enclave_binary: PathBuf,

    /// Path to the Oak Functions application binary to be loaded into the enclave.
    #[arg(long, value_parser = path_exists)]
    pub app_binary: PathBuf,

    /// Path to the BIOS image to use.
    #[arg(long, value_parser = path_exists)]
    pub bios_binary: PathBuf,

    /// Port to use for debugging with gdb
    #[arg(long = "gdb")]
    pub gdb: Option<u16>,
}

/// Writes a chunk to a channel, and expects an acknowledgement containing the length of the chunk.
fn write_chunk(channel: &mut dyn Channel, chunk: &[u8]) -> Result<()> {
    channel.write(chunk)?;
    let mut ack: [u8; 4] = Default::default();
    channel.read(&mut ack)?;
    if u32::from_le_bytes(ack) as usize != chunk.len() {
        anyhow::bail!("ack wasn't of correct length");
    }
    Ok(())
}

pub struct Instance {
    console: UnixStream,
    comms: UnixStream,
    instance: tokio::process::Child,
}

impl Instance {
    pub fn start(params: Params, console: UnixStream) -> Result<Self> {
        let app_bytes = fs::read(&params.app_binary).with_context(|| {
            format!(
                "couldn't read application binary {}",
                &params.app_binary.display()
            )
        })?;
        log::info!(
            "read application binary from disk {} ({} bytes)",
            &params.app_binary.display(),
            app_bytes.len()
        );

        let mut cmd = tokio::process::Command::new(params.vmm_binary);
        let (comms_guest, mut comms_host) = UnixStream::pair()?;

        cmd.stderr(Stdio::inherit());
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::inherit());
        cmd.preserved_fds(vec![console.as_raw_fd(), comms_guest.as_raw_fd()]);

        // Construct the command-line arguments for `qemu`.
        cmd.arg("-enable-kvm");
        // Needed to expose advanced CPU features. Specifically RDRAND which is required for remote
        // attestation.
        cmd.args(["-cpu", "IvyBridge-IBRS,enforce"]);

        // Disable a bunch of hardware we don't need.
        cmd.arg("-nodefaults");
        cmd.arg("-nographic");
        // If the VM restarts, don't restart it (we're not expecting any restarts so any restart
        // should be treated as a failure)
        cmd.arg("-no-reboot");
        // Use the `microvm` machine as the basis, and ensure ACPI is enabled.
        cmd.args(["-machine", "microvm,acpi=on"]);
        // Route first serial port to console.
        cmd.args([
            "-chardev",
            format!("socket,id=consock,fd={}", console.as_raw_fd()).as_str(),
        ]);
        cmd.args(["-serial", "chardev:consock"]);
        // Add the virtio device.
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
        // And yes, use stage0 as the BIOS.
        cmd.args([
            "-bios",
            params
                .bios_binary
                .into_os_string()
                .into_string()
                .unwrap()
                .as_str(),
        ]);

        if let Some(gdb_port) = params.gdb {
            // Listen for a gdb connection on the provided port and wait for debugger before booting
            cmd.args(["-gdb", format!("tcp::{}", gdb_port).as_str()]);
            cmd.arg("-S");
        }

        info!("Executing: {:?}", cmd);

        let instance = cmd.spawn()?;

        // Loading the application binary needs to happen before we start using microrpc over the
        // channel.
        comms_host
            .write(&(app_bytes.len() as u32).to_le_bytes())
            .expect("failed to send application binary length to enclave");

        // The kernel expects data to be transmitted in chunks of one page.
        let mut chunks = app_bytes.array_chunks::<PAGE_SIZE>();
        for chunk in chunks.by_ref() {
            write_chunk(&mut comms_host, chunk)?;
        }
        write_chunk(&mut comms_host, chunks.remainder())?;

        Ok(Self {
            instance,
            console,
            comms: comms_host,
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
