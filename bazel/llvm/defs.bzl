#
# Copyright 2025 The Project Oak Authors
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

"""Download the LLVM toolchain that Oak uses"""

load("@toolchains_llvm//toolchain:deps.bzl", "bazel_toolchain_dependencies")
load("@toolchains_llvm//toolchain:rules.bzl", "llvm_toolchain")

def setup_llvm_toolchains():
    """Download the LLVM toolchain that Oak uses"""

    bazel_toolchain_dependencies()

    llvm_toolchain(
        name = "llvm_toolchain",
        link_flags = {
            "none-x86_64": [
                "-nostdlib",
            ],
        },
        llvm_version = "20.1.0",
        sysroot = {
            "linux-x86_64": "@@oak_cc_toolchain_sysroot//:sysroot",
        },
    )
