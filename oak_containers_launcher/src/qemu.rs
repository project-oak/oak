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

use std::{
    io::{BufRead, BufReader},
    net::Ipv4Addr,
    os::{fd::AsRawFd, unix::net::UnixStream},
    path::PathBuf,
    process::Stdio,
};

use anyhow::Result;
use clap::Parser;
use command_fds::CommandFdExt;

use crate::path_exists;

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

    /// How many CPUs to give to the VM.
    #[arg(long, default_value_t = 1)]
    pub num_cpus: u8,

    /// Size (in kilobytes) of the ramdrive used for the system root.
    #[arg(long)]
    pub ramdrive_size: u32,

    /// Optional port where QEMU will start a telnet server for the serial console; useful for
    /// interactive debugging.
    #[arg(long)]
    pub telnet_console: Option<u16>,
}

impl Params {
    pub fn default_for_root(root: &str) -> Self {
        let vmm_binary = which::which("qemu-system-x86_64").expect("could not find qemu path");
        let stage0_binary =
            format!("{root}stage0_bin/target/x86_64-unknown-none/release/stage0_bin",).into();
        let kernel = format!("{root}oak_containers_kernel/target/bzImage",).into();
        let initrd = format!("{root}/target/stage1.cpio").into();
        Self {
            vmm_binary,
            stage0_binary,
            kernel,
            initrd,
            memory_size: Some("8G".to_owned()),
            num_cpus: 2,
            ramdrive_size: 3_000_000,
            telnet_console: None,
        }
    }
}

pub struct Qemu {
    instance: tokio::process::Child,
}

impl Qemu {
    pub fn start(
        params: Params,
        launcher_service_port: u16,
        host_proxy_port: u16,
        host_orchestrator_proxy_port: u16,
    ) -> Result<Self> {
        let mut cmd = tokio::process::Command::new(params.vmm_binary);
        let (guest_socket, host_socket) = UnixStream::pair()?;
        cmd.kill_on_drop(true);
        cmd.stderr(Stdio::inherit());
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::inherit());

        // Extract the raw file descriptor numbers from the streams before passing them to the child
        // process, since that takes ownership of them.
        let guest_socket_fd = guest_socket.as_raw_fd();

        cmd.preserved_fds(vec![guest_socket.into()]);

        // Construct the command-line arguments for `qemu`.
        cmd.arg("-enable-kvm");
        // Needed to expose advanced CPU features. Specifically RDRAND which is required for remote
        // attestation.
        cmd.args(["-cpu", "host"]);
        // Set memory size if given.
        if let Some(memory_size) = params.memory_size {
            cmd.args(["-m", &memory_size]);
        };
        // Number of CPUs to give to the VM.
        cmd.args(["-smp", format!("{}", params.num_cpus).as_str()]);
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
                format!("telnet:localhost:{port},server").as_str(),
            ]);
        } else {
            cmd.args([
                "-chardev",
                format!("socket,id=consock,fd={guest_socket_fd}").as_str(),
            ]);
            cmd.args(["-serial", "chardev:consock"]);
        }
        // Set up the networking. `rombar=0` is so that QEMU wouldn't bother with the
        // `efi-virtio.rom` file, as we're not using EFI anyway.
        let vm_address = crate::VM_LOCAL_ADDRESS;
        let vm_port = crate::VM_LOCAL_PORT;
        let vm_orchestrator_port = crate::VM_ORCHESTRATOR_LOCAL_PORT;
        let host_address = Ipv4Addr::LOCALHOST;
        cmd.args([
            "-netdev",
            [
                "user",
                "id=netdev",
                &format!(
                    "guestfwd=tcp:10.0.2.100:8080-cmd:nc {host_address} {launcher_service_port}"
                ),
                &format!("hostfwd=tcp:{host_address}:{host_proxy_port}-{vm_address}:{vm_port}"),
                &format!("hostfwd=tcp:{host_address}:{host_orchestrator_proxy_port}-{vm_address}:{vm_orchestrator_port}"),
            ]
            .join(",")
            .as_str(),
        ]);
        cmd.args(["-device", "virtio-net,netdev=netdev,rombar=0"]);
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
            "-kernel",
            params
                .kernel
                .into_os_string()
                .into_string()
                .unwrap()
                .as_str(),
        ]);
        cmd.args([
            "-initrd",
            params
                .initrd
                .into_os_string()
                .into_string()
                .unwrap()
                .as_str(),
        ]);
        let ramdrive_size = params.ramdrive_size;
        cmd.args([
            "-append",
            [
                params.telnet_console.map_or_else(|| "", |_| "debug"),
                "console=ttyS0",
                "panic=-1",
                "brd.rd_nr=1",
                format!("brd.rd_size={ramdrive_size}").as_str(),
                "brd.max_part=1",
                format!("ip={vm_address}:::255.255.255.0::eth0:off").as_str(),
                "quiet",
            ]
            .join(" ")
            .as_str(),
        ]);

        log::debug!("QEMU command line: {:?}", cmd);

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

    pub async fn kill(&mut self) -> Result<std::process::ExitStatus> {
        self.instance.start_kill()?;
        self.wait().await
    }

    pub async fn wait(&mut self) -> Result<std::process::ExitStatus> {
        self.instance.wait().await.map_err(anyhow::Error::from)
    }
}
