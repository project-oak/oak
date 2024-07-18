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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("//bazel:defs.bzl", "either_platform", "select_std_crates")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_virtio",
    srcs = glob(["src/**"]),
    target_compatible_with = either_platform([
        "//:x86_64-none-setting",
        "//:x86_64-linux-setting",  # Needed for unit testing.
    ]),
    deps = [
        "//third_party/rust-hypervisor-firmware-virtio",
        "@oak_crates_index//:strum",
    ] +
    # TODO: b/347706173 - Try to reduce / remove items in this select by moving all to no_std.
    select_std_crates([
        "anyhow",
        "bitflags",
        "log",
        "x86_64",
    ]),
)

rust_test(
    name = "oak_virtio_test",
    size = "small",
    crate = ":oak_virtio",
    deps = [
        "@oak_crates_index//:rand",
    ],
)
