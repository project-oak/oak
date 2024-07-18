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

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_binary(
    name = "sev_snp_hello_world_kernel",
    srcs = glob(["src/**/*.rs"]),
    compile_data = ["src/asm/boot.s"],
    linker_script = ":layout.ld",
    target_compatible_with = [
        "//:x86_64-none-setting",
    ],
    deps = [
        "//oak_linux_boot_params",
        "//oak_sev_guest:oak_sev_guest_no_rust_crypto",
        "//sev_serial:sev_serial_no_rust_crypto",
        "@oak_no_std_crates_index//:lazy_static",
        "@oak_no_std_crates_index//:lock_api",
        "@oak_no_std_crates_index//:log",
        "@oak_no_std_crates_index//:spinning_top",
        "@oak_no_std_crates_index//:x86_64",
    ],
)
