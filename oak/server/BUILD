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

package(
    default_visibility = ["//oak/server:__subpackages__"],
)

load("//oak/server:wabt.bzl", "wasm_group")

# Mark tests that can be run on the host system (i.e. with a normal
# compiler, not the Asylo toolchain) with 'host' tag.
test_suite(
    name = "host_tests",
    tags = ["host"],
)

cc_library(
    name = "oak_node",
    srcs = [
        "oak_node.cc",
        "wabt_output.cc",
    ],
    hdrs = [
        "oak_node.h",
        "wabt_output.h",
    ],
    deps = [
        ":channel",
        "//oak/common:handles",
        "//oak/proto:application_cc_grpc",
        "//oak/proto:grpc_encap_cc_proto",
        "//oak/proto:oak_api_cc_proto",
        "@boringssl//:crypto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/time",
        "@com_google_absl//absl/types:span",
        "@com_google_asylo//asylo/util:logging",
        "@wabt",
    ],
)

cc_test(
    name = "oak_node_test",
    srcs = [
        "oak_node_test.cc",
        "wabt_output_test.cc",
    ],
    data = [
        ":testdata",
    ],
    tags = ["host"],
    deps = [
        ":oak_node",
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

cc_library(
    name = "module_invocation",
    srcs = ["module_invocation.cc"],
    hdrs = ["module_invocation.h"],
    deps = [
        ":oak_node",
        "//oak/proto:grpc_encap_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_asylo//asylo/util:logging",
    ],
)

cc_library(
    name = "oak_runtime",
    srcs = ["oak_runtime.cc"],
    hdrs = ["oak_runtime.h"],
    deps = [
        ":module_invocation",
        ":oak_node",
        "//oak/proto:enclave_cc_proto",
        "//oak/server:logging_node",
        "//oak/server/storage:storage_node",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/synchronization",
        "@com_google_asylo//asylo/util:logging",
        "@com_google_asylo//asylo/util:status",
    ],
)

cc_library(
    name = "channel",
    srcs = ["channel.cc"],
    hdrs = ["channel.h"],
    deps = [
        "@com_google_absl//absl/synchronization",
        "@com_google_absl//absl/types:span",
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
        "@com_google_asylo//asylo/util:logging",
    ],
)
