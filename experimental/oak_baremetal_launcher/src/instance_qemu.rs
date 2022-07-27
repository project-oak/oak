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

use crate::{instance::LaunchedInstance, VmParams};
use anyhow::Result;
use async_trait::async_trait;
use command_fds::{tokio::CommandFdAsyncExt, FdMapping};
use log::info;
use std::{
    ffi::OsStr,
    net::Shutdown,
    os::unix::{io::AsRawFd, net::UnixStream},
    process::Stdio,
};

pub struct QemuInstance {
    console: UnixStream,
    comms_guest: UnixStream,
    comms_host: UnixStream,
    qmp: UnixStream,
    instance: tokio::process::Child,
}

impl QemuInstance {
    pub fn start(params: VmParams, console: UnixStream) -> Result<Self> {
        let (comms_guest, comms_host) = UnixStream::pair()?;
        let mut cmd = tokio::process::Command::new(params.vmm_binary);

        // There should not be any communication over stdin/stdout/stderr, but let's inherit
        // stderr just in case.
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::inherit());
        cmd.stderr(Stdio::inherit());

        // We're keeping the QMP socket to ourselves.
        let qmp = UnixStream::pair()?;

        // Set up the plumbing for communication sockets
        cmd.fd_mappings(vec![
            FdMapping {
                parent_fd: console.as_raw_fd(),
                child_fd: 10,
            },
            FdMapping {
                parent_fd: comms_guest.as_raw_fd(),
                child_fd: 11,
            },
            FdMapping {
                parent_fd: qmp.1.as_raw_fd(),
                child_fd: 12,
            },
        ])?;

        // Construct the command-line arguments for `qemu`. See
        // https://www.qemu.org/docs/master/system/invocation.html for all available options.

        // Needed to expose advanced CPU features to the bare-metal app. Specifically
        // RDRAND which is required for remote attestation.
        cmd.arg("-enable-kvm");
        cmd.args(&["-cpu", "IvyBridge-IBRS,enforce"]);
        // We're going to run qemu as a noninteractive embedded program, so disable any
        // graphical outputs.
        cmd.arg("-nographic");
        // Don't bother with default hardware, such as a VGA adapter, floppy drive, etc.
        cmd.arg("-nodefaults");
        // If the VM exits for some reason, don't reboot, but rather exit qemu as well, as
        // that's an erroneous situation.
        cmd.arg("-no-reboot");

        if let Some(gdb_port) = params.gdb {
            // Listen for a gdb connection on the provided port
            cmd.args(&["-gdb", format!("tcp::{}", gdb_port).as_str()]);
            // Wait for debugger before booting
            cmd.arg("-S");
            // Enable inspection of memory with gdb after a triple fault
            cmd.arg("-no-shutdown");
        }

        // Use the more modern `q35` machine as the basis.
        // TODO(#2679): q35 comes with a ton of stuff we don't need (eg a PC speaker). We
        // should use something simpler (microvm?), if possible.
        cmd.args(&[
            "-machine",
            "q35,usb=off,sata=off,smbus=off,graphics=off,vmport=off,smm=off",
        ]);
        // Add the qemu isa-debug-exit device. This can be used to exit qemu with a status
        // code within the VM.
        cmd.args(&["-device", "isa-debug-exit,iobase=0xf4,iosize=0x04"]);
        // First serial port: this will be used by the console.
        cmd.args(&["-chardev", "socket,id=consock,fd=10"]);
        cmd.args(&["-serial", "chardev:consock"]);
        // We use a simple virtio PCI serial port for host-guest communications.
        cmd.args(&["-chardev", "socket,id=commsock,fd=11"]);
        cmd.args(&[
            "-device",
            "virtio-serial-pci-non-transitional,id=virtio_serial_pci0,max_ports=1",
        ]);
        cmd.args(&[
            "-device",
            "virtconsole,chardev=commsock,bus=virtio_serial_pci0.0",
        ]);
        // Expose the QEMU monitor (QMP) over a socket as well.
        cmd.args(&["-chardev", "socket,id=qmpsock,fd=12"]);
        cmd.args(&["-qmp", "chardev:qmpsock"]);

        cmd.args(&[OsStr::new("-kernel"), params.app_binary.as_os_str()]);

        info!("Executing: {:?}", cmd);

        Ok(QemuInstance {
            instance: cmd.spawn()?,
            console,
            comms_guest,
            comms_host,
            qmp: qmp.0,
        })
    }
}

#[async_trait]
impl LaunchedInstance for QemuInstance {
    async fn wait(&mut self) -> Result<std::process::ExitStatus> {
        self.instance.wait().await.map_err(anyhow::Error::from)
    }

    async fn kill(mut self: Box<Self>) -> Result<std::process::ExitStatus> {
        info!("Cleaning up and shutting down.");
        self.console.shutdown(Shutdown::Both)?;
        self.comms_guest.shutdown(Shutdown::Both)?;
        self.qmp.shutdown(Shutdown::Both)?;
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
