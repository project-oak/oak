#
# Copyright 2026 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "oak_restricted_kernel_bin_tdx_virtio_console_channel",
    srcs = ["src/main.rs"],
    crate_features = ["virtio_console_channel"],
    linker_script = "//oak_restricted_kernel:layout.ld",
    platform = "//:x86_64-unknown-none",
    target_compatible_with = ["@platforms//cpu:x86_64"],
    deps = [
        "//oak_linux_boot_params",
        "//oak_restricted_kernel:oak_restricted_kernel_virtio_console_channel",
        "//oak_restricted_kernel_tdx:oak_restricted_kernel_tdx_virtio_console_channel",
    ],
)

rust_binary(
    name = "oak_restricted_kernel_bin_tdx_simple_io_channel",
    srcs = ["src/main.rs"],
    crate_features = ["simple_io_channel"],
    linker_script = "//oak_restricted_kernel:layout.ld",
    platform = "//:x86_64-unknown-none",
    target_compatible_with = ["@platforms//cpu:x86_64"],
    deps = [
        "//oak_linux_boot_params",
        "//oak_restricted_kernel:oak_restricted_kernel_simple_io_channel",
        "//oak_restricted_kernel_tdx:oak_restricted_kernel_tdx_simple_io_channel",
    ],
)

rust_binary(
    name = "oak_restricted_kernel_bin_tdx_serial_channel",
    srcs = ["src/main.rs"],
    crate_features = ["serial_channel"],
    linker_script = "//oak_restricted_kernel:layout.ld",
    platform = "//:x86_64-unknown-none",
    target_compatible_with = ["@platforms//cpu:x86_64"],
    deps = [
        "//oak_linux_boot_params",
        "//oak_restricted_kernel:oak_restricted_kernel_serial_channel",
        "//oak_restricted_kernel_tdx:oak_restricted_kernel_tdx_serial_channel",
    ],
)
