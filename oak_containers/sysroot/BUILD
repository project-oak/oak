# Copyright 2025 Google LLC.
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

load("@rules_distroless//distroless:defs.bzl", "flatten")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(licenses = ["notice"])

pkg_tar(
    name = "sysroot_overlay",
    srcs = ["BUILD.sysroot"],
    remap_paths = {"BUILD.sysroot": "BUILD"},
)

flatten(
    name = "sysroot",
    compress = "xz",
    tars = [
        ":sysroot_overlay",
        "@sysroot",
    ],
)

# Skip the xz step so it's bit faster to iterate.
# A convenience rule for iterating on the sysroot developement.
flatten(
    name = "sysroot-dev",
    tars = [
        ":sysroot_overlay",
        "@sysroot",
    ],
)

sh_binary(
    name = "push",
    srcs = ["push.sh"],
    data = [":sysroot"],
)
