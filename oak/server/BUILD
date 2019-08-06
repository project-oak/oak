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
        ":buffer_channel",
        ":channel",
        ":logging_channel",
        ":status",
        "//oak/common:handles",
        "//oak/proto:application_cc_grpc",
        "@boringssl//:crypto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/memory",
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
        "testdata/minimal_fini.wat",
        "testdata/missing_handle.wat",
        "testdata/missing_init.wat",
        "testdata/wrong_fini.wat",
        "testdata/wrong_handle.wat",
        "testdata/wrong_init.wat",
    ],
)

cc_library(
    name = "module_invocation",
    srcs = ["module_invocation.cc"],
    hdrs = ["module_invocation.h"],
    deps = [
        ":oak_node",
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
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/synchronization",
        "@com_google_asylo//asylo/util:logging",
        "@com_google_asylo//asylo/util:status",
    ],
)

cc_library(
    name = "channel",
    hdrs = ["channel.h"],
    deps = [],
)

cc_library(
    name = "buffer_channel",
    hdrs = ["buffer_channel.h"],
    deps = [
        ":channel",
    ],
)

cc_library(
    name = "logging_channel",
    hdrs = ["logging_channel.h"],
    deps = [
        ":channel",
    ],
)

cc_library(
    name = "status",
    hdrs = ["status.h"],
    deps = [],
)
