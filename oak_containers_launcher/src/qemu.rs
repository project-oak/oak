//
// Copyright 2023 The Project Oak Authors
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

use crate::path_exists;
use anyhow::Result;
use clap::Parser;
use command_fds::tokio::CommandFdAsyncExt;
use std::{
    io::{BufRead, BufReader},
    os::{fd::AsRawFd, unix::net::UnixStream},
    path::PathBuf,
    process::Stdio,
};

/// Represents parameters used for launching VM instances.
#[derive(Parser, Clone, Debug, PartialEq)]
pub struct Params {
    /// Path to the VMM binary to execute.
    #[arg(long, value_parser = path_exists)]
    pub vmm_binary: PathBuf,

    /// Path to the stage0 image to use.
    #[arg(long, value_parser = path_exists)]
    pub stage0_binary: PathBuf,

    /// Path to the Linux kernel file to use.
    #[arg(long, value_parser = path_exists)]
    pub kernel: PathBuf,

    /// Path to the initrd image to use.
    #[arg(long, value_parser = path_exists)]
    pub initrd: PathBuf,

    /// How much memory to give to the enclave binary, e.g., 256M (M stands for Megabyte, G for
    /// Gigabyte).
    #[arg(long)]
    pub memory_size: Option<String>,

    /// Size (in kilobytes) of the ramdrive used for the system root.
    #[arg(long)]
    pub ramdrive_size: u32,

    /// Optional port where QEMU will start a telnet server for the serial console; useful for
    /// interactive debugging.
    #[arg(long)]
    pub telnet_console: Option<u16>,
}

pub struct Qemu {
    instance: tokio::process::Child,
}

impl Qemu {
    pub fn start(params: Params) -> Result<Self> {
        let mut cmd = tokio::process::Command::new(params.vmm_binary);
        let (guest_socket, host_socket) = UnixStream::pair()?;

        cmd.stderr(Stdio::inherit());
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::inherit());
        cmd.preserved_fds(vec![guest_socket.as_raw_fd()]);

        // Construct the command-line arguments for `qemu`.
        cmd.arg("-enable-kvm");
        // Needed to expose advanced CPU features. Specifically RDRAND which is required for remote
        // attestation.
        cmd.args(["-cpu", "host"]);
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
        // Use the `microvm` machine as the basis, and ensure ACPI and PCIe are enabled.
        cmd.args(["-machine", "microvm,acpi=on,pcie=on"]);
        // Route first serial port to console.
        if let Some(port) = params.telnet_console {
            cmd.args([
                "-serial",
                format!("telnet:localhost:{},server", port).as_str(),
            ]);
        } else {
            cmd.args([
                "-chardev",
                format!("socket,id=consock,fd={}", guest_socket.as_raw_fd()).as_str(),
            ]);
            cmd.args(["-serial", "chardev:consock"]);
        }
        // Set up the networking. `rombar=0` is so that QEMU wouldn't bother with the
        // `efi-virtio.rom` file, as we're not using EFI anyway.
        cmd.args(["-netdev", "user,id=netdev"]);
        cmd.args(["-device", "virtio-net,netdev=netdev,rombar=0"]);
        // Set up the virtio-vsock device, as it is used by the example app.
        // TODO(#709): Remove this and use networking for there as well.
        cmd.args([
            "-device",
            format!(
                "vhost-vsock-pci,id=vhost-vsock-pci0,guest-cid={}",
                std::process::id()
            )
            .as_str(),
        ]);
        // And yes, use stage0 as the BIOS.
        cmd.args([
            "-bios",
            params
                .stage0_binary
                .into_os_string()
                .into_string()
                .unwrap()
                .as_str(),
        ]);
        // stage0 accoutrements: the kernel, initrd and inital kernel cmdline.
        cmd.args([
            "-fw_cfg",
            format!(
                "name=opt/stage0/elf_kernel,file={}",
                params
                    .kernel
                    .into_os_string()
                    .into_string()
                    .unwrap()
                    .as_str()
            )
            .as_str(),
        ]);
        cmd.args([
            "-fw_cfg",
            format!(
                "name=opt/stage0/initramfs,file={}",
                params
                    .initrd
                    .into_os_string()
                    .into_string()
                    .unwrap()
                    .as_str()
            )
            .as_str(),
        ]);
        cmd.args([
            "-fw_cfg",
            format!(
                "name=opt/stage0/cmdline,string={}",
                [
                    "console=ttyS0",
                    "panic=-1",
                    "brd.rd_nr=1",
                    format!("brd.rd_size={}", params.ramdrive_size).as_str(),
                    "brd.max_part=1",
                    "ip=10.0.2.10:::255.255.255.0::eth0:off"
                ]
                .join(" ")
            )
            .as_str(),
        ]);

        println!("QEMU command line: {:?}", cmd);

        // Spit out everything we read, if we were not using telnet console.
        if params.telnet_console.is_none() {
            tokio::spawn(async {
                let mut reader = BufReader::new(host_socket);

                let mut line = String::new();
                while reader.read_line(&mut line).expect("couldn't read line") > 0 {
                    print!("{}", line);
                    line.clear();
                }
            });
        }

        let instance = cmd.spawn()?;

        Ok(Self { instance })
    }

    pub async fn wait(&mut self) -> Result<std::process::ExitStatus> {
        self.instance.wait().await.map_err(anyhow::Error::from)
    }
}
