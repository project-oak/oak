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

use std::{
    fs,
    io::{BufRead, BufReader},
    net::Shutdown,
    os::{
        fd::AsRawFd,
        unix::{net, net::UnixStream},
    },
    path::PathBuf,
    process::Stdio,
};

use anyhow::{Context, Result};
use async_trait::async_trait;
use clap::Parser;
use command_fds::CommandFdExt;
use log::info;

use crate::channel::{Connector, ConnectorHandle};

/// Represents parameters used for launching VM instances.
#[derive(Parser, Clone, Debug, PartialEq)]
pub struct Params {
    /// Path to the VMM binary to execute.
    #[arg(long, value_parser = path_exists, value_name = "FILE")]
    pub vmm_binary: PathBuf,

    /// Path to the enclave binary to load into the VM.
    #[arg(long, value_parser = path_exists, value_name = "FILE")]
    pub kernel: PathBuf,

    /// Path to the Oak Functions application binary to be loaded into the
    /// enclave.
    #[arg(long, value_parser = path_exists, value_name = "FILE")]
    pub app_binary: Option<PathBuf>,

    /// Path to the BIOS image to use.
    #[arg(long, value_parser = path_exists, value_name = "FILE")]
    pub bios_binary: PathBuf,

    /// Port to use for debugging with gdb
    #[arg(long, value_name = "PORT")]
    pub gdb: Option<u16>,

    /// How much memory to give to the enclave binary, e.g., 256M (M stands for
    /// Megabyte, G for Gigabyte).
    #[arg(long)]
    pub memory_size: Option<String>,

    /// Path to the initrd image to use.
    #[arg(long, value_parser = path_exists, requires_all = &["kernel"], value_name = "FILE")]
    pub initrd: PathBuf,

    /// Pass the specified host PCI device through to the virtual machine using
    /// VFIO.
    #[arg(long, value_name = "ADDRESS")]
    pub pci_passthrough: Option<String>,
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
    /// Starts virtualized instance with given parameters and stream to write
    /// console logs to.
    pub fn start(params: Params, guest_console: net::UnixStream) -> Result<Self> {
        let app_bytes = if let Some(app_binary) = params.app_binary {
            let bytes = fs::read(&app_binary).with_context(|| {
                format!("couldn't read application binary {}", app_binary.display())
            })?;
            log::info!(
                "read application binary from disk {} ({} bytes)",
                app_binary.display(),
                bytes.len()
            );
            Some(bytes)
        } else {
            None
        };

        let mut cmd = tokio::process::Command::new(params.vmm_binary);
        let (guest_socket, mut host_socket) = net::UnixStream::pair()?;

        // Clone the console stream so we can use it in the child process and also
        // return it from this method.
        let guest_console_clone = guest_console.try_clone().unwrap();

        // Extract the raw file descriptor numbers from the streams before passing them
        // to the child process, since that takes ownership of them.
        let guest_console_fd = guest_console.as_raw_fd();
        let guest_socket_fd = guest_socket.as_raw_fd();

        cmd.stderr(Stdio::inherit());
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::inherit());
        cmd.preserved_fds(vec![guest_console.into(), guest_socket.into()]);

        // Construct the command-line arguments for `qemu`.
        cmd.arg("-enable-kvm");
        // Needed to expose advanced CPU features. Specifically RDRAND which is required
        // for remote attestation.
        cmd.args(["-cpu", "IvyBridge-IBRS,enforce"]);
        // Set memory size if given.
        if let Some(memory_size) = params.memory_size {
            cmd.args(["-m", &memory_size]);
        };
        // Disable a bunch of hardware we don't need.
        cmd.arg("-nodefaults");
        cmd.arg("-nographic");
        // If the VM restarts, don't restart it (we're not expecting any restarts so any
        // restart should be treated as a failure)
        cmd.arg("-no-reboot");
        // Use the `microvm` machine as the basis, and ensure ACPI is enabled.
        cmd.args(["-machine", "microvm,acpi=on"]);
        // Route first serial port to console.
        cmd.args(["-chardev", format!("socket,id=consock,fd={guest_console_fd}").as_str()]);
        cmd.args(["-serial", "chardev:consock"]);
        // Add the virtio device.
        cmd.args(["-chardev", format!("socket,id=commsock,fd={guest_socket_fd}").as_str()]);
        cmd.args(["-device", "virtio-serial-device,max_ports=1"]);
        cmd.args(["-device", "virtconsole,chardev=commsock"]);
        if let Some(pci_passthrough) = params.pci_passthrough {
            cmd.args(["-device", format!("vfio-pci,host={pci_passthrough}").as_str()]);
        }
        // Use stage0 as the BIOS.
        cmd.args(["-bios", params.bios_binary.into_os_string().into_string().unwrap().as_str()]);
        // stage0 accoutrements: kernel that's compatible with the linux boot protocol
        cmd.args(["-kernel", params.kernel.into_os_string().into_string().unwrap().as_str()]);

        if let Some(gdb_port) = params.gdb {
            // Listen for a gdb connection on the provided port and wait for debugger before
            // booting
            cmd.args(["-gdb", format!("tcp::{gdb_port}").as_str()]);
            cmd.arg("-S");
        }

        cmd.args(["-initrd", params.initrd.into_os_string().into_string().unwrap().as_str()]);

        info!("executing: {:?}", cmd);

        let instance = cmd.spawn()?;

        if let Some(app_bytes) = app_bytes {
            oak_channel::basic_framed::send_raw(&mut host_socket, &app_bytes)
                .context("failed to send application")?;
            #[cfg(feature = "exchange_evidence")]
            let _evidence = oak_channel::basic_framed::receive_raw(&mut host_socket)
                .context("failed to receive attestion evidence")?;
        }

        Ok(Self { guest_console: guest_console_clone, host_socket, instance })
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

/// Defines the interface of a launched guest instance. Standardizes the
/// interface of different implementations, e.g. a VM in which the guest is
/// running or the guest running directly as a unix binary.
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
                // remove the new line character
                line.pop();
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
