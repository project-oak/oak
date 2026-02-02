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

load(":umoci_toolchain.bzl", "umoci_toolchain")

package(licenses = ["notice"])

toolchain_type(
    name = "toolchain_type",
    visibility = ["//visibility:public"],
)

umoci_toolchain(
    name = "umoci",
    bin = "umoci.amd64",
)

toolchain(
    name = "umoci_toolchain",
    exec_compatible_with = [
        "@platforms//os:linux",
        "@platforms//cpu:x86_64",
    ],
    toolchain = ":umoci",
    toolchain_type = ":toolchain_type",
)
