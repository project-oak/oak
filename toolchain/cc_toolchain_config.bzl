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

"""This file is configuring the toolchain to use for wasm32, which is clang and llvm.
It overwrites the tool paths to point to clang and sets the needed flags for different
types of actions.
"""

load(
    "@bazel_tools//tools/cpp:cc_toolchain_config_lib.bzl",
    "feature",
    "flag_group",
    "flag_set",
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

all_compile_actions = [
    ACTION_NAMES.c_compile,
    ACTION_NAMES.cpp_compile,
    ACTION_NAMES.linkstamp_compile,
    ACTION_NAMES.assemble,
    ACTION_NAMES.preprocess_assemble,
    ACTION_NAMES.cpp_header_parsing,
    ACTION_NAMES.cpp_module_compile,
    ACTION_NAMES.cpp_module_codegen,
    ACTION_NAMES.clif_match,
    ACTION_NAMES.lto_backend,
]

def _impl(ctx):
    # Overwrite the paths to point to clang.
    # TODO: Bazel has a limitation as these paths can be only relative to the toolchain folder.
    # The hack around this is to have a script file that just redirects to the correct binary.
    # We need to fix this once Bazel does this properly.
    if ctx.attr.cpu == "armv8":
        clang = "clang_arm.sh"
    else:
        clang = "clang.sh"

    tool_paths = [
        tool_path(
            name = "gcc",
            path = clang,
        ),
        tool_path(
            name = "ld",
            path = clang,
        ),
        tool_path(
            name = "ar",
            path = "ar.sh",
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

    # aarch64 linux gnu cross compile flags
    arm_compile_flags = feature(
        name = "arm_compile_flags",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = all_compile_actions,
                flag_groups = [
                    flag_group(
                        flags = [
                            # sysroot that has all the includes.
                            "--sysroot=external/gcc_arm/aarch64-linux-gnu/libc",
                            # Path to get all the .so files we needed.
                            "--gcc-toolchain=external/gcc_arm",
                            # Compile for aarch64 linux.
                            "--target=aarch64-linux-gnu",
                            # Use armv8a architecture.
                            "-march=armv8a",
                            # Make the include paths absolute, not relative to clang binary
                            "-no-canonical-prefixes",
                        ],
                    ),
                ],
            ),
        ],
    )

    arm_link_flags = feature(
        name = "arm_link_flags",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = [ACTION_NAMES.cpp_link_executable],
                flag_groups = [
                    flag_group(
                        flags = [
                            # Use lld as the linker as it is faster and shows better error messages.
                            "-fuse-ld=lld",
                            # sysroot that has all the includes.
                            "--sysroot=external/gcc_arm/aarch64-linux-gnu/libc",
                            # Path to get all the .so files we needed.
                            "--gcc-toolchain=external/gcc_arm",
                            # Compile for aarch64 linux.
                            "--target=aarch64-linux-gnu",
                            # Use armv8a architecture.
                            "-march=armv8a",
                            # Because we use clang to build everything (instead of clang++), we need
                            # to remind it to link the correct stdc++ library.
                            "-lstdc++",
                        ],
                    ),
                ],
            ),
        ],
    )

    k8_link_flags = feature(
        name = "k8_link_flags",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = [ACTION_NAMES.cpp_link_executable],
                flag_groups = [
                    flag_group(
                        flags = [
                            # Use lld as the linker as it is faster and shows better error messages.
                            "-fuse-ld=lld",
                            # Because we use clang to build everything (instead of clang++), we need
                            # to remind it to link the correct stdc++ library.
                            "-lstdc++",
                        ],
                    ),
                ],
            ),
        ],
    )

    k8_compile_flags = feature(
        name = "k8_compile_flags",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = all_compile_actions,
                flag_groups = [
                    flag_group(
                        flags = [
                            # Make the include paths absolute, not relative to clang binary
                            "-no-canonical-prefixes",
                        ],
                    ),
                ],
            ),
        ],
    )

    # Setup the correct flags for compile + link + lto
    wasm_compile_flags = feature(
        name = "wasm_compile_flags",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = all_compile_actions,
                flag_groups = [
                    flag_group(
                        flags = [
                            "--target=wasm32-unknown-unknown",
                            # Module is built in freestanding mode.
                            "-ffreestanding",
                            # Do not try to use any standard includes for C or C++
                            "-nostdinc",
                            "-nostdinc++",
                            # Make the include paths absolute, not relative to clang binary
                            "-no-canonical-prefixes",
                            # Bazel require explicit include paths for system headers
                            "-isystem",
                            "external/clang/lib/clang/8.0.0/include",
                        ],
                    ),
                ],
            ),
        ],
    )

    # Flags to pass to lld.
    wasm_link_flags = feature(
        name = "wasm_link_flags",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = all_link_actions,
                flag_groups = [
                    flag_group(
                        flags = [
                            "--target=wasm32-unknown-unknown",
                            # Make sure we don't link stdlib.
                            "-nostdlib",
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

    host_system_name = "local"
    target_libc = "unknown"
    compiler = "clang"

    if (ctx.attr.cpu == "k8"):
        target_cpu = "k8"
        target_system_name = "local"
        abi_version = "local"
        abi_libc_version = "local"
        cxx_builtin_include_directories = [
            "/usr/include",
        ]
        features = [
            k8_compile_flags,
            k8_link_flags,
        ]
        toolchain_identifier = "clang-toolchain_k8"
    elif (ctx.attr.cpu == "armv8"):
        target_cpu = "armv8a"
        target_system_name = "aarch64"
        abi_version = "aarch64-linux-gnu"
        abi_libc_version = "aarch64-linux-gnu"
        cxx_builtin_include_directories = []
        features = [
            arm_compile_flags,
            arm_link_flags,
        ]
        toolchain_identifier = "clang-toolchain_armv8"
    elif (ctx.attr.cpu == "wasm32"):
        target_cpu = "wasm32"
        target_system_name = "wasm32-unknown-unknown"
        abi_version = "unknown"
        abi_libc_version = "unknown"
        cxx_builtin_include_directories = []
        features = [
            wasm_compile_flags,
            wasm_link_flags,
        ]
        toolchain_identifier = "clang-toolchain_wasm32"
    else:
        fail("Unreachable")

    # Put everythign together and return a config_info.
    return cc_common.create_cc_toolchain_config_info(
        ctx = ctx,
        cxx_builtin_include_directories = cxx_builtin_include_directories,
        toolchain_identifier = toolchain_identifier,
        host_system_name = host_system_name,
        target_system_name = target_system_name,
        target_cpu = target_cpu,
        target_libc = target_libc,
        compiler = compiler,
        abi_version = abi_version,
        abi_libc_version = abi_libc_version,
        tool_paths = tool_paths,
        features = features,
    )

cc_toolchain_config = rule(
    implementation = _impl,
    attrs = {
        "cpu": attr.string(mandatory = True, values = ["k8", "wasm32", "armv8"]),
    },
    provides = [CcToolchainConfigInfo],
)
