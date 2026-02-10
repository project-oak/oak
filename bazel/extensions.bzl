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

"""Module extensions for Oak toolchains."""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("//bazel/tools/umoci:umoci_toolchain.bzl", "umoci_toolchain_repo")

SYSROOT_SHA256 = "232d0363c317c72266e872a7e17829e8f7819ac4f1a4cd229518c4d475277472"

def _oak_toolchains_impl(_ctx):
    umoci_toolchain_repo(name = "umoci")
    http_archive(
        name = "oak_cc_toolchain_sysroot",
        sha256 = SYSROOT_SHA256,
        url = "https://storage.googleapis.com/oak-bins/sysroot/{}.tar.xz".format(SYSROOT_SHA256),
    )

oak_toolchains = module_extension(
    implementation = _oak_toolchains_impl,
)
