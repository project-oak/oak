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

package(
    default_visibility = ["//oak/server:__pkg__"],
)

# Mark tests that can be run on the host system (i.e. with a normal
# compiler, not the Asylo toolchain) with 'host' tag.
test_suite(
    name = "host_tests",
    tags = ["host"],
)

cc_binary(
    name = "storage_server",
    srcs = ["storage_server.cc"],
    deps = [
        # TODO: Fix grpc::Status.
        #        ":spanner_provider",
        ":storage_service",
        ":memory_provider",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/strings",
        "@com_google_asylo//asylo/util:logging",
    ],
)

cc_library(
    name = "storage_node",
    srcs = ["storage_node.cc"],
    hdrs = ["storage_node.h"],
    deps = [
        "//oak/common:app_config",
        "//oak/common:handles",
        "//oak/proto:storage_cc_grpc",
        "//oak/proto:storage_channel_cc_proto",
        "//oak/server:channel",
        "//oak/server:node_thread",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/memory",
        "@com_google_asylo//asylo/util:logging",
    ],
)

cc_library(
    name = "storage_manager",
    srcs = [
        "storage_manager.h",
    ],
    deps = [
        "@com_google_absl//absl/types:span",
    ],
)

cc_library(
    name = "storage_provider",
    hdrs = [
        "storage_provider.h",
    ],
    deps = [
        "//oak/proto:storage_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
    ],
)

cc_library(
    name = "storage_service",
    srcs = [
        "storage_service.cc",
    ],
    hdrs = [
        "storage_service.h",
    ],
    deps = [
        ":storage_provider",
        "//oak/proto:storage_cc_grpc",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_asylo//asylo/util:logging",
    ],
)

cc_library(
    name = "spanner_provider",
    srcs = [
        "spanner_provider.cc",
    ],
    hdrs = [
        "spanner_provider.h",
    ],
    deps = [
        ":storage_provider",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_asylo//asylo/util:logging",
        # TODO: Fix grpc::Status.
        #        "@com_google_googleapis//google/spanner/v1:spanner_cc_grpc",
    ],
)

cc_library(
    name = "memory_provider",
    srcs = ["memory_provider.cc"],
    hdrs = ["memory_provider.h"],
    deps = [
        ":storage_provider",
        "@com_google_absl//absl/strings",
    ],
)

cc_test(
    name = "memory_provider_test",
    srcs = ["memory_provider_test.cc"],
    tags = ["host"],
    deps = [
        ":memory_provider",
        "@gtest//:gtest_main",
    ],
)
