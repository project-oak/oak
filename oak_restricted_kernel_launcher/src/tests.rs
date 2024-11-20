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
// See the License for the speific language governing permissions and
// limitations under the License.

//! Integration tests for the Oak Functions Launcher.

use oak_echo_service::proto::oak::echo;
use oak_file_utils::data_path;
use oak_launcher_utils::launcher;

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_echo_enclave_app_launch() {
    let oak_restricted_kernel_orchestrator_app_path =
        data_path("enclave_apps/oak_orchestrator/oak_orchestrator");

    let oak_echo_enclave_app_path =
        data_path("enclave_apps/oak_echo_enclave_app/oak_echo_enclave_app");

    let params = launcher::Params {
        kernel: data_path("oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin"),
        vmm_binary: which::which("qemu-system-x86_64").unwrap(),
        app_binary: Some(oak_echo_enclave_app_path),
        bios_binary: data_path("stage0_bin/stage0_bin"),
        gdb: None,
        initrd: oak_restricted_kernel_orchestrator_app_path,
        memory_size: Some("256M".to_string()),
        pci_passthrough: None,
    };
    println!("launcher params: {:?}", params);

    let (_guest_instance, connector_handle) =
        launcher::launch(params).await.expect("failed to launch");

    println!("Launched!");
    let mut client = echo::EchoAsyncClient::new(connector_handle);

    let message = b"Hello World";
    let request = echo::EchoRequest { body: message.to_vec() };
    let result =
        client.echo(&request).await.expect("failed to invoke method").expect("invocation failed");
    assert_eq!(result.body, message);
}
