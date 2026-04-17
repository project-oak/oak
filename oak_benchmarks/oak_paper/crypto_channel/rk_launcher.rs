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

use std::{cell::RefCell, rc::Rc};

use message_stream_client::MessageStream;
use oak_channel::message::RequestMessage;
use oak_file_utils::data_path;
use oak_launcher_utils::launcher;

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
    fn read_message(&mut self) -> Vec<u8> {
        let (msg, _timer) =
            self.oak_client_channel.borrow_mut().read_response().expect("failed to read message");
        msg.body
    }

    fn send_message(&mut self, msg: &[u8]) {
        self.oak_client_channel
            .borrow_mut()
            .write_request(RequestMessage { invocation_id: 0, body: msg.to_vec() })
            .expect("failed to read message");
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
    let params = launcher::Params {
        kernel,
        vmm_binary: which::which("qemu-system-x86_64").unwrap(),
        app_binary: Some(app),
        bios_binary: data_path("stage0_bin/stage0_bin"),
        gdb: None,
        initrd: oak_restricted_kernel_orchestrator_app_path,
        memory_size: Some("256M".to_string()),
        pci_passthrough: None,
        initial_data_version,
        communication_channel,
        vm_type: launcher::VmType::Default,
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
