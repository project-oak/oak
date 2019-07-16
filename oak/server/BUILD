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

load(
    "@com_google_asylo//asylo/bazel:asylo.bzl",
    "enclave_loader",
    "sim_enclave",
)
load("@linux_sgx//:sgx_sdk.bzl", "sgx_enclave_configuration")
load("//oak/server:wabt.bzl", "wasm_group")

cc_library(
    name = "oak_manager",
    srcs = [
        "oak_manager.cc",
    ],
    hdrs = [
        "oak_manager.h",
    ],
    deps = [
        "//oak/proto:application_cc_grpc",
        "//oak/proto:enclave_cc_proto",
        "//oak/proto:manager_cc_grpc",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/strings",
        "@com_google_asylo//asylo:enclave_client",
        "@com_google_asylo//asylo/grpc/util:enclave_server_cc_proto",
        "@com_google_asylo//asylo/identity:descriptions",
        "@com_google_asylo//asylo/identity:enclave_assertion_authority_config_cc_proto",
        "@com_google_asylo//asylo/util:logging",
    ],
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
        ":buffer_channel",
        ":channel",
        ":logging_channel",
        ":status",
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

cc_library(
    name = "enclave_server",
    srcs = [
        "enclave_server.cc",
    ],
    hdrs = [
        "enclave_server.h",
    ],
    deps = [
        ":module_invocation",
        ":oak_node",
        "//oak/proto:enclave_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/synchronization",
        "@com_google_asylo//asylo:enclave_runtime",
        "@com_google_asylo//asylo/grpc/auth:grpc++_security_enclave",
        "@com_google_asylo//asylo/grpc/auth:null_credentials_options",
        "@com_google_asylo//asylo/grpc/util:enclave_server_cc_proto",
        "@com_google_asylo//asylo/util:logging",
        "@com_google_asylo//asylo/util:status",
    ],
)

sgx_enclave_configuration(
    name = "grpc_enclave_config",
    # gRPC needs more than the default amount of heap to run. ~1.2GB.
    heap_max_size = "0x47000000",
    tcs_num = "200",
)

sim_enclave(
    name = "oak_enclave.so",
    srcs = [
        "oak_enclave.cc",
    ],
    config = "grpc_enclave_config",
    deps = [
        ":enclave_server",
        "@com_google_asylo//asylo/grpc/util:enclave_server",
    ],
)

enclave_loader(
    name = "oak",
    srcs = ["oak_main.cc"],
    enclaves = {"enclave": ":oak_enclave.so"},
    loader_args = ["--enclave_path='{enclave}'"],
    deps = [
        ":oak_manager",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/synchronization",
        "@com_google_absl//absl/time",
        "@com_google_asylo//asylo/util:logging",
    ],
)
