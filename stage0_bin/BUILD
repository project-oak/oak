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
load("//bazel:defs.bzl", "objcopy")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "stage0_bin_elf",
    srcs = glob(["src/**/*.rs"]),
    aliases = {
        "@//stage0": "oak_stage0",
        "@//stage0_sev": "oak_stage0_sev",
    },
    compile_data = [
        "src/asm/boot.s",
        "src/asm/ap_boot.s",
        "src/asm/reset_vector.s",
    ],
    linker_script = ":layout.ld",
    platform = "//:x86_64-firmware",
    rustc_flags = [
        "--codegen=opt-level=z",
        "--codegen=lto=fat",
        "--codegen=link-arg=-Wl,--defsym=BIOS_SIZE=512K",
        "--codegen=relocation-model=static",
        "--codegen=link-arg=-static",
        "--codegen=link-arg=-Wl,-static",
    ],
    tags = ["no-clippy"],
    deps = [
        "//stage0",
        "//stage0_sev",
    ],
)

objcopy(
    name = "stage0_bin",
    src = ":stage0_bin_elf",
)
