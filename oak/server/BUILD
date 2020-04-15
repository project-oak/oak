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

load("@rules_cc//cc:defs.bzl", "cc_library")

package(
    default_visibility = ["//oak/server:__subpackages__"],
    licenses = ["notice"],
)

cc_library(
    name = "oak_node",
    srcs = ["oak_node.cc"],
    hdrs = ["oak_node.h"],
    deps = [
        "//oak/common:handles",
        "//oak/common:logging",
        "//oak/proto:label_cc_proto",
        "//oak/proto:oak_abi_cc_proto",
        "//oak/server/rust/oak_glue:oak_glue_wrapper",
        "@com_google_absl//absl/base:endian",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/synchronization",
    ],
)

cc_library(
    name = "handle_closer",
    hdrs = ["handle_closer.h"],
    deps = [":oak_node"],
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
        ":oak_node",
        "//oak/common:handles",
        "//oak/common:label",
        "//oak/common:logging",
        "//oak/proto:grpc_encap_cc_proto",
        "//oak/proto:label_cc_proto",
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
        ":grpc_client_node",
        ":oak_grpc_node",
        ":oak_node",
        ":roughtime_client_node",
        "//oak/common:app_config",
        "//oak/common:logging",
        "//oak/proto:oak_abi_cc_proto",
        "//oak/server/rust/oak_glue:oak_glue_wrapper",
        "//oak/server/storage:storage_node",
        "@com_google_absl//absl/base",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/strings",
        "@com_google_absl//absl/synchronization",
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
        ":invocation",
        ":oak_node",
        "//oak/common:handles",
        "//oak/common:logging",
        "//oak/proto:grpc_encap_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/memory",
    ],
)

cc_library(
    name = "roughtime_client_node",
    srcs = ["roughtime_client_node.cc"],
    hdrs = ["roughtime_client_node.h"],
    deps = [
        ":invocation",
        ":oak_node",
        "//oak/common:handles",
        "//oak/common:logging",
        "//oak/proto:application_cc_proto",
        "//oak/proto:grpc_encap_cc_proto",
        "//oak/proto:roughtime_service_cc_proto",
        "//oak/server/time:roughtime_client",
        "@com_google_absl//absl/memory",
    ],
)
