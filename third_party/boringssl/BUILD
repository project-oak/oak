#
# Copyright 2026 The Project Oak Authors
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

load("@rules_cc//cc:cc_library.bzl", "cc_library")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

# BoringSSL crypto library wrapped for Oak Restricted Kernel.
#
# This cc_library provides the BoringSSL crypto library configured for
# the freestanding x86_64-unknown-none environment.  It re-exports
# @boringssl//:crypto with the LLVM libc and libc++ dependencies needed
# on the os:none platform.
#
# The Rust crates (bssl_sys, bssl_macros, bssl_crypto) are defined in
# the BoringSSL external repo itself at @boringssl//rust via
# rust/BUILD.bazel (created by patch_cmds in MODULE.bazel).
cc_library(
    name = "boringssl_crypto",
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
    ],
    deps = [
        "//third_party/llvm_libc:llvm_libc",
        "//third_party/llvm_libc:llvm_libcxx",
        "@boringssl//:crypto",
    ],
)
