#
# Copyright 2019 The Project Oak Authors
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

# This file is configuring the toolchain to use for wasm32, which is clang and llvm.
# It overwrites the tool paths to point to clang and sets the needed flags for different
# types of actions.

load(
    "@bazel_tools//tools/cpp:cc_toolchain_config_lib.bzl",
    "action_config",
    "feature",
    "flag_group",
    "flag_set",
    "tool",
    "tool_path",
)
load("@bazel_tools//tools/build_defs/cc:action_names.bzl", "ACTION_NAMES")

all_link_actions = [
    ACTION_NAMES.cpp_link_executable,
    ACTION_NAMES.cpp_link_dynamic_library,
    ACTION_NAMES.cpp_link_nodeps_dynamic_library,
    ACTION_NAMES.cpp_link_static_library,
]

lto_index_actions = [
    ACTION_NAMES.lto_index_for_executable,
    ACTION_NAMES.lto_index_for_dynamic_library,
    ACTION_NAMES.lto_index_for_nodeps_dynamic_library,
]

all_cpp_compile_actions = [
    ACTION_NAMES.cpp_compile,
    ACTION_NAMES.linkstamp_compile,
    ACTION_NAMES.cpp_header_parsing,
    ACTION_NAMES.cpp_module_compile,
    ACTION_NAMES.cpp_module_codegen,
    ACTION_NAMES.clif_match,
]

def _impl(ctx):
    # Overwrite the paths to point to clang.
    # TODO: Bazel has a limitation as these paths can be only relative to the toolchain folder.
    # The hack around this is to have a script file that just redirects to the correct binary.
    # We need to fix this once Bazel does this properly.
    tool_paths = [
        tool_path(
            name = "gcc",
            path = "clang.sh",
        ),
        tool_path(
            name = "ld",
            path = "clang.sh",
        ),
        tool_path(
            name = "ar",
            path = "/bin/false",
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

    # Setup the correct flags for compile + link + lto
    wasm_flags = feature(
        name = "wasm_flags",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = all_cpp_compile_actions + all_link_actions + lto_index_actions,
                flag_groups = [
                    flag_group(
                        flags = [
                            "-ffreestanding",
                            # Bazel require explicit include paths for system headers
                            "-isystem",
                            "external/clang_llvm/lib/clang/8.0.0/include",
                            "-isystem",
                            "external/clang_llvm/include/c++/v1/",
                            "--target=wasm32-unknown-unknown",
                            # Make sure we don't link stdlib
                            "-nostdlib",
                        ],
                    ),
                ],
            ),
        ],
    )

    # Flags to pass to lld.
    link_flags = feature(
        name = "link_flags",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = all_link_actions,
                flag_groups = [
                    flag_group(
                        flags = [
                            # No main file for wasm.
                            "--for-linker",
                            "-no-entry",
                            # Export symbol in the executable which are marked as
                            # visibility=default.
                            "--for-linker",
                            "--export-dynamic",
                            # Allow undefined symbols. These will be defined by the wasm vm.
                            "--for-linker",
                            "--allow-undefined",
                        ],
                    ),
                ],
            ),
        ],
    )

    # Put everythign together and return a config_info.
    return cc_common.create_cc_toolchain_config_info(
        ctx = ctx,
        toolchain_identifier = "clang_llvm-toolchain",
        host_system_name = "i686-unknown-linux-gnu",
        target_system_name = "wasm32-unknown-unknown",
        target_cpu = "wasm32",
        target_libc = "unknown",
        compiler = "clang",
        abi_version = "unknown",
        abi_libc_version = "unknown",
        tool_paths = tool_paths,
        features = [
            wasm_flags,
            link_flags,
        ],
    )

cc_toolchain_config = rule(
    implementation = _impl,
    attrs = {},
    provides = [CcToolchainConfigInfo],
)
