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

cc_library(
    name = "oak_node",
    srcs = ["oak_node.cc"],
    hdrs = ["oak_node.h"],
    deps = [
        ":base_runtime",
        ":channel",
        "//oak/common:handles",
        "//oak/common:logging",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/synchronization",
    ],
)

cc_library(
    name = "handle_closer",
    hdrs = ["handle_closer.h"],
    deps = [":oak_node"],
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
        ":channel",
        "//oak/common:handles",
        "//oak/common:logging",
        "//oak/proto:grpc_encap_cc_proto",
        "//oak/proto:oak_api_cc_proto",
        "//oak/server:node_thread",
        "@com_google_absl//absl/base:endian",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/time",
        "@com_google_absl//absl/types:span",
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
        "//oak/common:logging",
        "//oak/common:policy",
        "//oak/proto:grpc_encap_cc_proto",
        "//oak/proto:policy_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/synchronization",
    ],
)

cc_library(
    name = "oak_runtime",
    srcs = ["oak_runtime.cc"],
    hdrs = [
        "oak_runtime.h",
    ],
    deps = [
        ":base_runtime",
        ":grpc_client_node",
        ":oak_grpc_node",
        ":wasm_node",
        "//oak/common:app_config",
        "//oak/common:logging",
        "//oak/proto:oak_api_cc_proto",
        "//oak/server:logging_node",
        "//oak/server/storage:storage_node",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/strings",
        "@com_google_absl//absl/synchronization",
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
        ":notification",
        "//oak/common:logging",
        "//oak/proto:oak_api_cc_proto",
        "//oak/proto:policy_cc_proto",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/synchronization",
        "@com_google_absl//absl/types:variant",
    ],
)

cc_test(
    name = "channel_test",
    srcs = ["channel_test.cc"],
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
        "//oak/common:logging",
    ],
)

cc_library(
    name = "logging_node",
    srcs = ["logging_node.cc"],
    hdrs = ["logging_node.h"],
    deps = [
        ":handle_closer",
        ":node_thread",
        "//oak/common:handles",
        "//oak/common:logging",
        "//oak/proto:log_cc_proto",
        "@com_google_absl//absl/memory",
    ],
)

cc_library(
    name = "invocation",
    srcs = ["invocation.cc"],
    hdrs = ["invocation.h"],
    deps = [
        ":handle_closer",
        ":oak_node",
        "//oak/common:handles",
        "//oak/common:logging",
        "@com_google_absl//absl/memory",
    ],
)

cc_library(
    name = "grpc_client_node",
    srcs = ["grpc_client_node.cc"],
    hdrs = ["grpc_client_node.h"],
    deps = [
        ":base_runtime",
        ":invocation",
        ":node_thread",
        "//oak/common:handles",
        "//oak/common:logging",
        "//oak/proto:grpc_encap_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/memory",
    ],
)

cc_library(
    name = "notification",
    srcs = ["notification.cc"],
    hdrs = ["notification.h"],
    deps = [
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/synchronization",
    ],
)

cc_test(
    name = "notification_test",
    srcs = ["notification_test.cc"],
    deps = [
        ":channel",
        ":notification",
        "//oak/common:logging",
        "@com_google_absl//absl/memory",
        "@gtest//:gtest_main",
    ],
)
