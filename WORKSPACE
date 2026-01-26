#
# Copyright 2018 The Project Oak Authors
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

workspace(name = "oak")

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

http_archive(
    name = "bazel_features",
    strip_prefix = "bazel_features-1.39.0",
    url = "https://github.com/bazel-contrib/bazel_features/releases/download/v1.39.0/bazel_features-v1.39.0.tar.gz",
)

load("@bazel_features//:deps.bzl", "bazel_features_deps")

bazel_features_deps()

load("@//bazel:repositories.bzl", "oak_toolchain_repositories")

oak_toolchain_repositories()

load("//bazel/llvm:deps.bzl", "load_llvm_repositories")

load_llvm_repositories()

load("//bazel/llvm:defs.bzl", "setup_llvm_toolchains")

setup_llvm_toolchains()

load("//bazel/llvm:reg.bzl", "register_llvm_toolchains")

register_llvm_toolchains()

load("//bazel/rust:defs.bzl", "setup_rust_dependencies")

setup_rust_dependencies()

load("//bazel/rust:stdlibs.bzl", "setup_rebuilt_rust_stdlibs")

setup_rebuilt_rust_stdlibs()

load("//bazel/crates:patched_crates.bzl", "load_patched_crates")

load_patched_crates()

load("//bazel/crates:repositories.bzl", "create_oak_crate_repositories")

create_oak_crate_repositories()

load("//bazel/crates:crates.bzl", "load_oak_crate_repositories")

load_oak_crate_repositories()
