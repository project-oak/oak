//
// Copyright 2026 The Project Oak Authors
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

use std::{cell::RefCell, env, fs, path::PathBuf, rc::Rc};

use clap::ValueEnum;
use message_stream_client::MessageStream;
use oak_channel::message::RequestMessage;
use oak_file_utils::data_path;
use oak_launcher_utils::launcher;

/// Selects the VM type, taking the same values as the launcher's `--vm-type`.
const VM_TYPE_ENV: &str = "RK_VM_TYPE";
/// Overrides the QEMU binary, which on a TEE host is often not on `PATH`.
const VMM_BINARY_ENV: &str = "RK_VMM_BINARY";

/// Which VM type the enclave legs launch.
///
/// Unset is `default`, an ordinary KVM guest with no memory encryption, which
/// is the only thing this benchmark could ask for before.
pub fn vm_type() -> launcher::VmType {
    let Ok(value) = env::var(VM_TYPE_ENV) else {
        return launcher::VmType::Default;
    };
    launcher::VmType::from_str(&value, true)
        .unwrap_or_else(|error| panic!("{VM_TYPE_ENV}={value}: {error}"))
}

/// Benchmark name infix for the VM type, empty for `default`.
///
/// A confidential guest is a different series, not a rerun of the same one.
/// `default` stays unmarked so names match logs taken before this existed.
pub fn vm_type_infix() -> String {
    match vm_type() {
        launcher::VmType::Default => String::new(),
        other => {
            format!(" [{}]", other.to_possible_value().expect("vm type is nameable").get_name())
        }
    }
}

/// QEMU to launch.
fn vmm_binary() -> PathBuf {
    match env::var(VMM_BINARY_ENV) {
        Ok(path) => PathBuf::from(path),
        Err(_) => which::which("qemu-system-x86_64").expect("no qemu-system-x86_64 on PATH"),
    }
}

/// Checks `/dev/sev` before asking QEMU for an SEV guest.
///
/// QEMU reports this as a generic launch failure after the benchmark has
/// already started, and the fix is a udev rule on the host, not a code change.
fn check_sev_device(vm_type: &launcher::VmType) {
    use launcher::VmType::{Default, Tdx};
    if matches!(vm_type, Default | Tdx) {
        return;
    }
    if let Err(error) = fs::OpenOptions::new().read(true).write(true).open("/dev/sev") {
        panic!(
            "{VM_TYPE_ENV} asks for an SEV guest but /dev/sev is unusable: {error}\n\
             grant the kvm group access, then log back in:\n  \
             echo 'KERNEL==\"sev\", MODE=\"0660\", GROUP=\"kvm\"' | \
             sudo tee /etc/udev/rules.d/71-sev.rules\n  \
             sudo udevadm control --reload && sudo udevadm trigger --name-match=sev"
        );
    }
}

pub struct OakClientChannelMessageStream {
    oak_client_channel: Rc<RefCell<oak_channel::client::ClientChannelHandle>>,
}

impl OakClientChannelMessageStream {
    pub fn new(
        oak_client_channel: &Rc<RefCell<oak_channel::client::ClientChannelHandle>>,
    ) -> OakClientChannelMessageStream {
        OakClientChannelMessageStream { oak_client_channel: oak_client_channel.clone() }
    }
}

impl MessageStream for OakClientChannelMessageStream {
    /// Never `None`: the enclave channel is a pair of file descriptors into a
    /// running guest, not a connection, so there is nothing that could close.
    fn try_read_message(&mut self) -> Option<Vec<u8>> {
        let (msg, _timer) =
            self.oak_client_channel.borrow_mut().read_response().expect("reading message");
        Some(msg.body)
    }

    fn send_message(&mut self, msg: &[u8]) {
        self.oak_client_channel
            .borrow_mut()
            .write_request(RequestMessage { invocation_id: 0, body: msg.to_vec() })
            .expect("writing message");
    }
}

pub async fn start_rk_enclave_server(
    mode: &[u8],
) -> (Box<dyn launcher::GuestInstance>, Rc<RefCell<oak_channel::client::ClientChannelHandle>>) {
    let oak_restricted_kernel_orchestrator_app_path =
        data_path("enclave_apps/oak_orchestrator/oak_orchestrator");

    let initial_data_version = launcher::InitialDataVersion::V1;
    let communication_channel = launcher::CommunicationChannel::VirtioConsole;
    let kernel = data_path(
        "oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin",
    );

    let app = data_path("oak_benchmarks/oak_paper/crypto_channel/rk_app");
    let vm_type = vm_type();
    check_sev_device(&vm_type);
    let params = launcher::Params {
        kernel,
        vmm_binary: vmm_binary(),
        app_binary: Some(app),
        bios_binary: data_path("stage0_bin/stage0_bin"),
        gdb: None,
        initrd: oak_restricted_kernel_orchestrator_app_path,
        memory_size: Some("1G".to_string()),
        pci_passthrough: None,
        initial_data_version,
        communication_channel,
        vm_type,
    };
    println!("launcher params: {:?}", params);

    let (guest_instance, _connector_handle) =
        launcher::launch(params).await.expect("failed to launch");

    let oak_client_channel = Rc::new(RefCell::new(oak_channel::client::ClientChannelHandle::new(
        guest_instance.connect().await.expect("couldn't get connector handle"),
    )));

    oak_client_channel
        .borrow_mut()
        .write_request(RequestMessage { invocation_id: 0, body: mode.to_vec() })
        .expect("couldn't write initial request");

    (guest_instance, oak_client_channel)
}
