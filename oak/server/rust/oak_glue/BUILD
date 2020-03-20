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

load("@io_bazel_rules_rust//rust:rust.bzl", "rust_library")
load("@rules_cc//cc:defs.bzl", "cc_library")

package(
    default_visibility = ["//oak/server:__subpackages__"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_glue",
    srcs = glob(["src/**/*.rs"]),
    crate_type = "staticlib",
    edition = "2018",
    deps = [
        "//cargo:byteorder",
        "//cargo:lazy_static",
        "//cargo:log",
        "//cargo:prost",
        "//cargo:simple_logger",
        "//oak/server/rust/oak_abi",
        "//oak/server/rust/oak_runtime",
    ],
)

# Wrapper rule to expose the resulting static library as a statically linked cc_library and
# corresponding header so that it can be depended on by other cc_library and cc_binary rules.
#
# TODO: There seems to be something wrong with this rule related to caching in Bazel.
# To reproduce:
# - change src/lib.rs and introduce a syntax error
# - bazel build :oak_glue_wrapper
# - this should produce a compile error, instead Bazel is still caching the old artifact
#
# However, building a cc_binary target (e.g. //oak/server/dev:dev_oak_runner) does force
# a rebuild of the Rust code.
cc_library(
    name = "oak_glue_wrapper",
    srcs = [":oak_glue"],
    hdrs = ["oak_glue.h"],
    linkopts = ["-ldl"],
    linkstatic = True,
)
