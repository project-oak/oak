#
# Copyright 2023 The Project Oak Authors
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

load(":cc_toolchain_config.bzl", "cc_toolchain_config")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_toolchain_config(name = "oak_toolchain_config")

filegroup(
    name = "wrappers",
    srcs = glob([
        "wrappers/**",
    ]),
)

filegroup(
    name = "all_files",
    srcs = [
        ":wrappers",
        "@x86_64-unknown-oak//:toolchain",
    ],
)

cc_toolchain(
    name = "oak_toolchain",
    all_files = ":all_files",
    compiler_files = ":all_files",
    dwp_files = ":empty",
    linker_files = ":all_files",
    objcopy_files = ":empty",
    strip_files = ":empty",
    toolchain_config = ":oak_toolchain_config",
    toolchain_identifier = "oak-toolchain",
)

toolchain(
    name = "oak",
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "//:os_oak",
    ],
    toolchain = ":oak_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)
