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

load(
    "@com_google_asylo//asylo/bazel:asylo.bzl",
    "enclave_loader",
    "sim_enclave",
)

load("@linux_sgx//:sgx_sdk.bzl", "sgx_enclave_configuration")

cc_library(
    name = "oak_server",
    srcs = [
        "oak_server.cc",
    ],
    hdrs = [
        "oak_server.h",
    ],
    deps = [
        ":enclave_server",
        "//oak/proto:oak_server_grpc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/memory",
        "@com_google_asylo//asylo/util:logging",
        "@wabt//:wabt",
    ],
)

cc_library(
    name = "enclave_server",
    hdrs = [
        "enclave_server.h",
    ],
    deps = [
        "//oak/proto:oak_proto_cc",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/synchronization",
        "@com_google_asylo//asylo:enclave_runtime",
        "@com_google_asylo//asylo/grpc/util:enclave_server_proto_cc",
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
        ":oak_server",
        "//oak/proto:oak_proto_cc",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/strings",
        "@com_google_asylo//asylo/grpc/auth:grpc++_security_enclave",
        "@com_google_asylo//asylo/grpc/auth:null_credentials_options",
        "@com_google_asylo//asylo:enclave_runtime",
        "@com_google_asylo//asylo/grpc/util:enclave_server",
        "@com_google_asylo//asylo/util:status",
    ],
)

enclave_loader(
    name = "oak",
    srcs = ["oak_driver.cc"],
    enclaves = {"enclave": ":oak_enclave.so"},
    loader_args = ["--enclave_path='{enclave}'"],
    deps = [
        "//oak/proto:oak_proto_cc",
        "//oak/proto:scheduling_service_grpc_proto",
        "@com_github_gflags_gflags//:gflags_nothreads",
        "@com_google_absl//absl/strings",
        "@com_google_absl//absl/synchronization",
        "@com_google_absl//absl/time",
        "@com_google_asylo//asylo:enclave_client",
        "@com_google_asylo//asylo/util:logging",
        "@com_google_asylo//asylo/grpc/util:enclave_server_proto_cc",
    ],
)
