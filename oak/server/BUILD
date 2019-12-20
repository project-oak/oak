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

load("@rules_cc//cc:defs.bzl", "cc_library", "cc_test")
load("//oak/common:fuzzer.bzl", "oak_fuzzer")
load("//oak/server:wabt.bzl", "wasm_group")

package(
    default_visibility = ["//oak/server:__subpackages__"],
    licenses = ["notice"],
)

# Mark tests that can be run on the host system (i.e. with a normal
# compiler, not the Asylo toolchain) with 'host' tag.
test_suite(
    name = "host_tests",
    tags = ["host"],
)

cc_library(
    name = "oak_node",
    srcs = ["oak_node.cc"],
    hdrs = ["oak_node.h"],
    deps = [
        ":channel",
        "//oak/common:handles",
        "@com_google_absl//absl/synchronization",
        "@com_google_asylo//asylo/util:logging",
    ],
)

cc_library(
    name = "wasm_node",
    srcs = [
        "wabt_output.cc",
        "wasm_node.cc",
    ],
    hdrs = [
        "wabt_output.h",
        "wasm_node.h",
    ],
    deps = [
        ":base_runtime",
        ":channel",
        "//oak/common:handles",
        "//oak/proto:grpc_encap_cc_proto",
        "//oak/proto:oak_api_cc_proto",
        "//oak/server:node_thread",
        "@com_google_absl//absl/base:endian",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/time",
        "@com_google_absl//absl/types:span",
        "@com_google_asylo//asylo/util:logging",
        "@wabt",
    ],
)

oak_fuzzer(
    name = "wasm_node_fuzz",
    srcs = [
        "wasm_node_fuzzer.cc",
    ],
    tags = ["manual"],  # requires main() from fuzzer
    deps = [
        ":wasm_node",
    ],
)

cc_test(
    name = "wasm_node_test",
    srcs = [
        "wabt_output_test.cc",
        "wasm_node_test.cc",
    ],
    data = [
        ":testdata",
    ],
    tags = ["host"],
    deps = [
        ":wasm_node",
        "@gtest//:gtest_main",
    ],
)

wasm_group(
    name = "testdata",
    srcs = [
        "testdata/empty.wat",
        "testdata/minimal.wat",
        "testdata/missing.wat",
        "testdata/wrong.wat",
    ],
)

# This should be the only target that depends on @com_github_grpc_grpc.
cc_library(
    name = "oak_grpc_node",
    srcs = [
        "module_invocation.cc",
        "oak_grpc_node.cc",
    ],
    hdrs = [
        "module_invocation.h",
        "oak_grpc_node.h",
    ],
    deps = [
        ":channel",
        ":oak_node",
        "//oak/common:app_config",
        "//oak/common:policy",
        "//oak/proto:application_cc_grpc",
        "//oak/proto:enclave_cc_proto",
        "//oak/proto:grpc_encap_cc_proto",
        "//oak/proto:policy_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/synchronization",
        "@com_google_asylo//asylo/grpc/auth:null_credentials_options",
        "@com_google_asylo//asylo/util:logging",
    ],
)

# Wrapper rule to expose the resulting static library as a statically linked cc_library and
# corresponding header so that it can be depended on by other cc_library and cc_binary rules.
#
# TODO: There seems to be something wrong with this rule related to caching in Bazel.
# To reproduce:
# - change src/lib.rs and introduce a syntax error
# - bazel build //rust/oak_runtime:wrapper
# - this should produce a compile error, instead Bazel is still caching the old artifact
# The final link of //oak/server/asylo:oak uses oak_runtime_stripped.a not libwrapper.a. Similarly,
# a change to the Rust file does induce a rebuild when doing bazel build //oak/server/dev:oak. So is
# Bazel maybe doing something special for a target with a single src that is itself a .a file?
cc_library(
    name = "rust_wrapper",
    srcs = ["//sdk/rust/oak_runtime_compat:oak_runtime_stripped"],
    linkstatic = True,
)

cc_library(
    name = "oak_runtime",
    srcs = ["oak_runtime.cc"],
    hdrs = [
        "oak_runtime.h",
        "rust_check.h",
    ],
    deps = [
        ":base_runtime",
        ":oak_grpc_node",
        ":rust_wrapper",
        ":wasm_node",
        "//oak/common:app_config",
        "//oak/proto:enclave_cc_proto",
        "//oak/proto:oak_api_cc_proto",
        "//oak/server:logging_node",
        "//oak/server/storage:storage_node",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/strings",
        "@com_google_absl//absl/synchronization",
        "@com_google_asylo//asylo/util:logging",
    ],
)

cc_library(
    name = "base_runtime",
    hdrs = ["base_runtime.h"],
    deps = [
        ":channel",
    ],
)

cc_library(
    name = "channel",
    srcs = ["channel.cc"],
    hdrs = ["channel.h"],
    deps = [
        "//oak/proto:oak_api_cc_proto",
        "//oak/proto:policy_cc_proto",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/synchronization",
        "@com_google_absl//absl/types:variant",
        "@com_google_asylo//asylo/util:logging",
    ],
)

cc_test(
    name = "channel_test",
    srcs = ["channel_test.cc"],
    tags = ["host"],
    deps = [
        ":channel",
        "@com_google_absl//absl/memory",
        "@gtest//:gtest_main",
    ],
)

cc_library(
    name = "node_thread",
    srcs = ["node_thread.cc"],
    hdrs = ["node_thread.h"],
    deps = [
        ":oak_node",
        "@com_google_asylo//asylo/util:logging",
    ],
)

cc_library(
    name = "logging_node",
    srcs = ["logging_node.cc"],
    hdrs = ["logging_node.h"],
    deps = [
        ":channel",
        ":node_thread",
        "//oak/common:app_config",
        "//oak/common:handles",
        "@com_google_absl//absl/memory",
        "@com_google_asylo//asylo/util:logging",
    ],
)
