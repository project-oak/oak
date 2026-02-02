#
# Copyright 2024 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_functions_test_utils",
    srcs = glob(["src/*.rs"]),
    data = [
        "//enclave_apps/oak_functions_enclave_app",
        "//enclave_apps/oak_orchestrator",
        "//oak_containers/stage1_bin",
        "//oak_containers/system_image:oak_containers_system_image",
        "//oak_functions_launcher",
        "//oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin",
        "//stage0_bin",
    ],
    deps = [
        "//oak_client",
        "//oak_file_utils",
        "//oak_functions_abi",
        "//oak_functions_client:lib",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:command-group",
        "@oak_crates_index//:http",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:once_cell",
        "@oak_crates_index//:port_check",
        "@oak_crates_index//:portpicker",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:tempfile",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:ubyte",
        "@oak_crates_index//:which",
    ],
)
