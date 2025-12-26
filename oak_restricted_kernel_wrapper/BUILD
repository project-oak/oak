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
load(":rules.bzl", "kernel_bzimage_and_measurements")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

kernel_bzimage_and_measurements(
    name = "oak_restricted_kernel_wrapper_virtio_console_channel",
    payload = "//oak_restricted_kernel_bin:oak_restricted_kernel_bin_virtio_console_channel",
)

kernel_bzimage_and_measurements(
    name = "oak_restricted_kernel_wrapper_simple_io_channel",
    payload = "//oak_restricted_kernel_bin:oak_restricted_kernel_bin_simple_io_channel",
)

kernel_bzimage_and_measurements(
    name = "oak_restricted_kernel_wrapper_serial_channel",
    payload = "//oak_restricted_kernel_bin:oak_restricted_kernel_bin_serial_channel",
)

kernel_bzimage_and_measurements(
    name = "stage0_test_kernel",
    payload = "//stage0/testing:test_kernel",
    visibility = ["//stage0:__subpackages__"],
)
