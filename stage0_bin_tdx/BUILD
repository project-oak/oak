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
    name = "stage0_bin_tdx_elf",
    srcs = glob(["src/**/*.rs"]),
    aliases = {"@//stage0": "oak_stage0"},
    compile_data = [
        "src/asm/reset_vector_tdx.s",
        "src/asm/tdx.s",
    ],
    linker_script = ":layout.ld",
    platform = "//:x86_64-firmware",
    rustc_flags = [
        "--codegen=relocation-model=static",
        "--codegen=opt-level=z",
        "--codegen=lto=fat",
        "--codegen=link-arg=-Wl,--defsym=BIOS_SIZE=2M",
        "--codegen=link-arg=-static",
        "--codegen=link-arg=-Wl,-static",
    ],
    tags = ["no-clippy"],
    deps = [
        "//oak_attestation",
        "//oak_dice",
        "//oak_linux_boot_params",
        "//oak_sev_snp_attestation_report",
        "//oak_tdx_guest",
        "//stage0",
        "//stage0_tdx",
        "@oak_crates_index//:log",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:zerocopy_08",
        "@oak_crates_index//:zeroize",
    ],
)

objcopy(
    name = "stage0_bin_tdx",
    src = ":stage0_bin_tdx_elf",
)
