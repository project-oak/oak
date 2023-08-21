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

use crate::channel::{Connector, ConnectorHandle};
use anyhow::{Context, Result};
use async_trait::async_trait;
use clap::Parser;
use command_fds::tokio::CommandFdAsyncExt;
use log::info;
use oak_channel::Write;
use std::{
    fs,
    io::{BufRead, BufReader},
    net::Shutdown,
    os::unix::{io::AsRawFd, net, net::UnixStream},
    path::PathBuf,
    process::Stdio,
};

const PAGE_SIZE: usize = 4096;

/// Represents parameters used for launching VM instances.
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

    /// How much memory to give to the enclave binary, e.g., 256M (M stands for Megabyte, G for
    /// Gigabyte).
    #[arg(long)]
    pub memory_size: Option<String>,
}

/// Checks if file with a given path exists.
fn path_exists(s: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(s);
    if !fs::metadata(s).map_err(|err| err.to_string())?.is_file() {
        Err(String::from("path does not represent a file"))
    } else {
        Ok(path)
    }
}

/// Represents an a guest instance launched in virtualized environment.
pub struct Instance {
    guest_console: net::UnixStream,
    host_socket: net::UnixStream,
    instance: tokio::process::Child,
}

impl Instance {
    /// Starts virtualized instance with given parameters and stream to write console logs to.
    pub fn start(params: Params, guest_console: net::UnixStream) -> Result<Self> {
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
        let (guest_socket, mut host_socket) = net::UnixStream::pair()?;

        cmd.stderr(Stdio::inherit());
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::inherit());
        cmd.preserved_fds(vec![guest_console.as_raw_fd(), guest_socket.as_raw_fd()]);

        // Construct the command-line arguments for `qemu`.
        cmd.arg("-enable-kvm");
        // Needed to expose advanced CPU features. Specifically RDRAND which is required for remote
        // attestation.
        cmd.args(["-cpu", "IvyBridge-IBRS,enforce"]);
        // Set memory size if given.
        if let Some(memory_size) = params.memory_size {
            cmd.args(["-m", &memory_size]);
        };
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
            format!("socket,id=consock,fd={}", guest_console.as_raw_fd()).as_str(),
        ]);
        cmd.args(["-serial", "chardev:consock"]);
        // Add the virtio device.
        cmd.args([
            "-chardev",
            format!("socket,id=commsock,fd={}", guest_socket.as_raw_fd()).as_str(),
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

        info!("executing: {:?}", cmd);

        let instance = cmd.spawn()?;

        // Loading the application binary needs to happen before we start using microrpc over the
        // channel.
        host_socket
            .write_all(&(app_bytes.len() as u32).to_le_bytes())
            .expect("failed to send application binary length to enclave");

        // The kernel expects data to be transmitted in chunks of one page.
        let mut chunks = app_bytes.array_chunks::<PAGE_SIZE>();
        for chunk in chunks.by_ref() {
            Self::write_chunk(&mut host_socket, chunk)?;
        }
        Self::write_chunk(&mut host_socket, chunks.remainder())?;

        Ok(Self {
            guest_console,
            host_socket,
            instance,
        })
    }

    /// Writes a chunk to a channel, and expects an acknowledgement containing the length of the
    /// chunk.
    fn write_chunk(channel: &mut dyn oak_channel::Channel, chunk: &[u8]) -> Result<()> {
        channel.write_all(chunk)?;
        let mut ack: [u8; 4] = Default::default();
        channel.read_exact(&mut ack)?;
        if u32::from_le_bytes(ack) as usize != chunk.len() {
            anyhow::bail!("ack wasn't of correct length");
        }
        Ok(())
    }
}

#[async_trait]
impl GuestInstance for Instance {
    async fn wait(&mut self) -> Result<std::process::ExitStatus> {
        info!("waiting for guest instance to terminate");
        self.instance.wait().await.map_err(anyhow::Error::from)
    }

    async fn kill(mut self: Box<Self>) -> Result<std::process::ExitStatus> {
        info!("killing guest instance; cleaning up and shutting down");
        self.guest_console.shutdown(Shutdown::Both)?;
        self.instance.start_kill()?;
        self.wait().await
    }

    async fn connect(&self) -> Result<Box<dyn oak_channel::Channel>> {
        info!("connecting to guest instance");
        Ok(Box::new(self.host_socket.try_clone()?))
    }
}

/// Defines the interface of a launched guest instance. Standardizes the interface of different
/// implementations, e.g. a VM in which the guest is running or the guest running directly as a
/// unix binary.
#[async_trait]
pub trait GuestInstance {
    /// Wait for the guest instance process to finish.
    async fn wait(&mut self) -> Result<std::process::ExitStatus>;

    /// Kill the guest instance.
    async fn kill(self: Box<Self>) -> Result<std::process::ExitStatus>;

    /// Creates a channel to communicate with the guest instance.
    async fn connect(&self) -> Result<Box<dyn oak_channel::Channel>>;
}

/// Launches a new guest instance in given mode.
pub async fn launch(
    params: Params,
) -> Result<(Box<dyn GuestInstance>, ConnectorHandle), Box<dyn std::error::Error>> {
    // Provide a way for the launched instance to send logs
    let guest_writer: UnixStream = {
        // Create two linked consoles. Technically both can read/write, but we'll
        // use them as a one way channel.
        let (console_writer, console_receiver) = UnixStream::pair()?;

        // Log everything sent by the writer.
        tokio::spawn(async {
            let mut reader = BufReader::new(console_receiver);

            let mut line = String::new();
            while reader.read_line(&mut line).expect("couldn't read line") > 0 {
                log::info!("console: {:?}", line);
                line.clear();
            }
        });

        console_writer
    };

    log::info!("launching instance");

    let guest_instance = Box::new(Instance::start(params, guest_writer)?);

    let channel = guest_instance.connect().await?;
    let connector_handle = Connector::spawn(channel);

    Ok((guest_instance, connector_handle))
}
