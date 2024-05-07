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
"""CC toolchain for bare metal."""

load("@bazel_tools//tools/cpp:cc_toolchain_config_lib.bzl", "tool_path")

# TODO: b/329826039 - these paths may hinder reproducibility, use nix paths.
def _cc_x86_64_unknown_none_toolchain_config_impl(ctx):
    tool_paths = [
        tool_path(
            name = "gcc",
            path = "/usr/bin/clang",
        ),
        tool_path(
            name = "ld",
            path = "/usr/bin/ld",
        ),
        tool_path(
            name = "ar",
            path = "/usr/bin/ar",
        ),
        tool_path(
            name = "cpp",
            path = "/bin/false",
        ),
        tool_path(
            name = "gcov",
            path = "/bin/false",
        ),
        tool_path(
            name = "nm",
            path = "/bin/false",
        ),
        tool_path(
            name = "objdump",
            path = "/bin/false",
        ),
        tool_path(
            name = "strip",
            path = "/bin/false",
        ),
    ]

    return cc_common.create_cc_toolchain_config_info(
        ctx = ctx,
        cxx_builtin_include_directories = [
            # TODO: b/329826039 - use nix.
            "/usr/lib/llvm-16/lib/clang/16/include",
            "/usr/include",
        ],
        toolchain_identifier = "x86_64-unknown-none-toolchain",
        host_system_name = "local",
        target_system_name = "freestanding",  # Required but deprecated.
        target_cpu = "x86_64",  # Required but deprecated.
        target_libc = "",
        compiler = "clang",
        abi_version = "unknown",
        abi_libc_version = "unknown",
        tool_paths = tool_paths,
    )

cc_x86_64_unknown_none_toolchain_config = rule(
    implementation = _cc_x86_64_unknown_none_toolchain_config_impl,
    attrs = {},
    provides = [CcToolchainConfigInfo],
)
