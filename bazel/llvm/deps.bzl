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

"""Setup the LLVM toolchain that Oak uses"""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

SYSROOT_SHA256 = "d6f608cf14b27bd4ae68f135b601b86bb9157a1a7a8fc08e43d7ff4ab7a18665"

def load_llvm_repositories(oak_repo_name = "oak"):
    """Setup the LLVM toolchain that Oak uses"""

    http_archive(
        name = "oak_cc_toolchain_sysroot",
        build_file = "@" + oak_repo_name + "//:toolchain/sysroot.BUILD",
        sha256 = SYSROOT_SHA256,
        url = "https://storage.googleapis.com/oak-bins/sysroot/" + SYSROOT_SHA256 + ".tar.xz",
    )

    http_archive(
        name = "toolchains_llvm",
        canonical_id = "v1.6.0",
        strip_prefix = "toolchains_llvm-v1.6.0",
        integrity = "sha256-KymKHX6plnn17fivCTZzY+ZMufvEbgt8GxuisbG1EFg=",
        url = "https://github.com/bazel-contrib/toolchains_llvm/releases/download/v1.6.0/toolchains_llvm-v1.6.0.tar.gz",
    )
