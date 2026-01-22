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
    net::{IpAddr, Ipv4Addr},
    os::{fd::AsRawFd, unix::net::UnixStream},
    path::PathBuf,
    process::Stdio,
};

use anyhow::Result;
use clap::Parser;
use command_fds::CommandFdExt;
pub use oak_launcher_utils::launcher::VmType;
use tokio_vsock::VMADDR_CID_HOST;

use crate::{path_exists, VM_HOST_ADDRESS, VM_HOST_PORT};

/// Represents parameters used for launching VM instances.
#[derive(Parser, Clone, Debug, PartialEq)]
pub struct Params {
    /// Path to the VMM binary to execute.
    #[arg(long, value_parser = path_exists, value_name = "FILE")]
    pub vmm_binary: PathBuf,

    /// Path to the stage0 image to use.
    #[arg(long, value_parser = path_exists, value_name = "FILE")]
    pub stage0_binary: PathBuf,

    /// Path to the Linux kernel file to use.
    #[arg(long, value_parser = path_exists, value_name = "FILE")]
    pub kernel: PathBuf,

    /// Path to the initrd image to use.
    #[arg(long, value_parser = path_exists, value_name = "FILE")]
    pub initrd: PathBuf,

    /// How much memory to give to the enclave binary, e.g., 256M (M stands for
    /// Megabyte, G for Gigabyte).
    #[arg(long)]
    pub memory_size: Option<String>,

    /// How many CPUs to give to the VM.
    #[arg(long, default_value_t = 1)]
    pub num_cpus: u8,

    /// Size (in kilobytes) of the ramdrive used for the system root.
    #[arg(long)]
    pub ramdrive_size: u32,

    /// Optional port where QEMU will start a telnet server for the serial
    /// console; useful for interactive debugging.
    #[arg(long, value_name = "PORT")]
    pub telnet_console: Option<u16>,

    /// Optional virtio guest CID for virtio-vsock. If not assigned, defaults to
    /// the current thread ID.
    /// Warning: This CID needs to be globally unique on the whole host!
    #[arg(long)]
    pub virtio_guest_cid: Option<u32>,

    /// Pass the specified host PCI device through to the virtual machine using
    /// VFIO.
    #[arg(long, value_name = "ADDRESS")]
    pub pci_passthrough: Option<String>,

    /// Type of the confidential VM. It could be Default, Sev, SevEs,
    /// SevSnp, or Tdx.
    #[arg(long, required = false, value_enum, default_value_t = VmType::Default)]
    pub vm_type: VmType,
}

pub enum Network {
    // Set up a network with the following proxy ports.
    Proxy {
        launcher_service_port: u16,
        host_proxy_port: Option<u16>,
        host_orchestrator_proxy_port: u16,
    },

    // Set up TAP networking.
    Tap {
        guest_address: IpAddr,
    },
}

impl Network {
    fn launcher_port(&self) -> u16 {
        match self {
            Network::Proxy { launcher_service_port, .. } => *launcher_service_port,
            Network::Tap { .. } => VM_HOST_PORT,
        }
    }

    /// Returns the address to be assigned to the guest.
    fn guest_address(&self) -> IpAddr {
        match self {
            Network::Proxy { .. } => crate::VM_LOCAL_ADDRESS,
            Network::Tap { guest_address } => *guest_address,
        }
    }

    /// Returns the address to be assigned to the guest with the correct
    /// netmask.
    fn guest_eth0_address(&self) -> String {
        match self.guest_address() {
            IpAddr::V4(guest_address) => format!("{}/24", guest_address),
            IpAddr::V6(guest_address) => format!("{}/64", guest_address),
        }
    }
}

pub struct Qemu {
    instance: tokio::process::Child,
    guest_cid: Option<u32>,
}

impl Qemu {
    pub fn start(params: Params, network: Network) -> Result<Self> {
        let mut cmd = tokio::process::Command::new(params.vmm_binary);
        let (guest_socket, host_socket) = UnixStream::pair()?;
        cmd.kill_on_drop(true);
        cmd.stderr(Stdio::inherit());
        cmd.stdin(Stdio::null());
        cmd.stdout(Stdio::inherit());

        // Extract the raw file descriptor numbers from the streams before passing them
        // to the child process, since that takes ownership of them.
        let guest_socket_fd = guest_socket.as_raw_fd();

        cmd.preserved_fds(vec![guest_socket.into()]);

        // Construct the command-line arguments for `qemu`.
        cmd.arg("-enable-kvm");
        // Needed to expose advanced CPU features. Specifically RDRAND which is required
        // for remote attestation.
        cmd.args(["-cpu", "host"]);
        // Set memory size if given.
        if let Some(ref memory_size) = params.memory_size {
            cmd.args(["-m", memory_size]);
        };
        // Number of CPUs to give to the VM.
        cmd.args(["-smp", format!("{}", params.num_cpus).as_str()]);
        // Disable a bunch of hardware we don't need.
        cmd.arg("-nodefaults");
        cmd.arg("-nographic");
        // If the VM restarts, don't restart it (we're not expecting any restarts so any
        // restart should be treated as a failure)
        cmd.arg("-no-reboot");
        // Use the `microvm` machine as the basis, and ensure ACPI and PCIe are enabled.
        let microvm_common = "microvm,acpi=on,pcie=on".to_string();
        // SEV, SEV-ES, SEV-SNP VMs need confidential guest support and private memory.
        let sev_machine_suffix = ",confidential-guest-support=sev0,memory-backend=ram1";
        // Definition of the private memory.
        let sev_common_object = format!(
            "memory-backend-memfd,id=ram1,size={},share=true,reserve=false",
            params.memory_size.clone().unwrap_or("8G".to_string())
        );
        // SEV's feature configuration.
        let sev_config_object = "id=sev0,cbitpos=51,reduced-phys-bits=1";
        // TDX machine suffix
        let tdx_machine_suffix = ",kernel_irqchip=split,memory-encryption=tdx,memory-backend=ram1";
        let tdx_common_object = format!(
            "memory-backend-ram,id=ram1,size={}",
            params.memory_size.unwrap_or("8G".to_string())
        );
        // Generate the parameters and add them to cmd.args.
        let (machine_arg, object_args) = match params.vm_type {
            VmType::Default => (microvm_common, vec![]),
            VmType::Sev => (
                microvm_common + sev_machine_suffix,
                vec![
                    sev_common_object,
                    "sev-guest,".to_string() + sev_config_object + ",policy=0x1",
                ],
            ),
            VmType::SevEs => (
                microvm_common + sev_machine_suffix,
                vec![
                    sev_common_object,
                    "sev-guest,".to_string() + sev_config_object + ",policy=0x5",
                ],
            ),
            VmType::SevSnp => (
                microvm_common + sev_machine_suffix,
                vec![
                    sev_common_object,
                    // Reference:
                    // https://lore.kernel.org/kvm/20240502231140.GC13783@ls.amr.corp.intel.com/T/
                    // A basic command-line invocation for SNP would be
                    // ...
                    // -object sev-snp-guest,id=sev0,cbitpos=51,reduced-phys-bits=1,id-auth=
                    // ...
                    "sev-snp-guest,".to_string() + sev_config_object + ",id-auth=",
                ],
            ),
            VmType::Tdx => (
                microvm_common + tdx_machine_suffix,
                // The command line comes from
                // https://patchwork.kernel.org/project/qemu-devel/patch/20240125032328.2522472-51-xiaoyao.li@intel.com/
                vec![r#"{"qom-type":"tdx-guest","id":"tdx","sept-ve-disable":true, "quote-generation-socket":{"type": "vsock", "cid":"2","port":"4050"}}"#.to_string(),
                    tdx_common_object],
            ),
        };
        cmd.args(["-machine", &machine_arg]);
        for obj_arg in object_args {
            cmd.args(["-object", &obj_arg]);
        }
        // Route first serial port to console.
        if let Some(port) = params.telnet_console {
            cmd.args(["-serial", format!("telnet:localhost:{port},server").as_str()]);
        } else {
            cmd.args(["-chardev", format!("socket,id=consock,fd={guest_socket_fd}").as_str()]);
            cmd.args(["-serial", "chardev:consock"]);
        }
        // Set up the networking. `rombar=0` is so that QEMU wouldn't bother with the
        // `efi-virtio.rom` file, as we're not using EFI anyway.
        let netdev_rules = match network {
            Network::Proxy {
                launcher_service_port,
                host_proxy_port,
                host_orchestrator_proxy_port,
            } => {
                let vm_address = network.guest_address();
                let vm_orchestrator_port = crate::VM_ORCHESTRATOR_LOCAL_PORT;
                let host_address = Ipv4Addr::LOCALHOST;

                let mut netdev_rules = vec![
                    "user".to_string(),
                    "id=netdev".to_string(),
                    format!("guestfwd=tcp:{VM_HOST_ADDRESS}:{VM_HOST_PORT}-cmd:nc {host_address} {launcher_service_port}"),
                    format!("hostfwd=tcp:{host_address}:{host_orchestrator_proxy_port}-{vm_address}:{vm_orchestrator_port}"),
                ];

                if let Some(host_proxy_port) = host_proxy_port {
                    let vm_port = crate::VM_LOCAL_PORT;
                    netdev_rules.push(format!(
                        "hostfwd=tcp:{host_address}:{host_proxy_port}-{vm_address}:{vm_port}"
                    ));
                };

                netdev_rules
            }
            Network::Tap { .. } => vec![
                "tap".to_string(),
                "id=netdev".to_string(),
                "ifname=oak0".to_string(),
                "script=no".to_string(),
            ],
        };
        cmd.args(["-netdev", netdev_rules.join(",").as_str()]);
        cmd.args([
            "-device",
            "virtio-net-pci,disable-legacy=on,iommu_platform=true,netdev=netdev,romfile=",
        ]);
        // The CID needs to be globally unique, so we default to the current thread ID
        // (which should be unique on the system). This may have interesting
        // interactions with async code though: if you start two VMMs in the same
        // thread, it won't work. But we don't really have any other good sources of
        // globally unique identifiers available for us, and starting multiple VMMs in
        // one thread should be uncommon.
        let virtio_guest_cid = params
            .virtio_guest_cid
            .unwrap_or_else(|| nix::unistd::gettid().as_raw().unsigned_abs());
        cmd.args(["-device", &format!("vhost-vsock-pci,guest-cid={virtio_guest_cid},rombar=0")]);

        if let Some(pci_passthrough) = params.pci_passthrough {
            cmd.args(["-device", format!("vfio-pci,host={pci_passthrough}").as_str()]);
        }
        // And yes, use stage0 as the BIOS.
        cmd.args(["-bios", params.stage0_binary.into_os_string().into_string().unwrap().as_str()]);
        // stage0 accoutrements: the kernel, initrd and inital kernel cmdline.
        cmd.args(["-kernel", params.kernel.into_os_string().into_string().unwrap().as_str()]);
        cmd.args(["-initrd", params.initrd.into_os_string().into_string().unwrap().as_str()]);
        let ramdrive_size = params.ramdrive_size;

        let cmdline = vec![
            params.telnet_console.map_or_else(|| "", |_| "debug").to_string(),
            "console=ttyS0".to_string(),
            "panic=-1".to_string(),
            "brd.rd_nr=1".to_string(),
            format!("brd.rd_size={ramdrive_size}"),
            "brd.max_part=1".to_string(),
            "loglevel=7".to_string(),
            "--".to_string(),
            format!("--eth0-address={}", network.guest_eth0_address()),
            format!("--launcher-addr=vsock://{VMADDR_CID_HOST}:{}", network.launcher_port()),
        ];

        cmd.args(["-append", cmdline.join(" ").as_str()]);

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

        Ok(Self { instance, guest_cid: params.virtio_guest_cid })
    }

    pub async fn kill(&mut self) -> Result<std::process::ExitStatus> {
        self.instance.start_kill()?;
        self.wait().await
    }

    pub async fn wait(&mut self) -> Result<std::process::ExitStatus> {
        self.instance.wait().await.map_err(anyhow::Error::from)
    }

    pub fn guest_cid(&self) -> Option<u32> {
        self.guest_cid
    }
}
