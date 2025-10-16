#
# Copyright 2024 The Project Oak Authors
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

load("@com_github_grpc_grpc//bazel:cc_grpc_library.bzl", "cc_grpc_library")
load("@com_google_protobuf//bazel:cc_proto_library.bzl", "cc_proto_library")
load("@rules_cc//cc:cc_binary.bzl", "cc_binary")
load("@rules_cc//cc:cc_library.bzl", "cc_library")
load("@rules_proto//proto:defs.bzl", "proto_library")
load("@rules_shell//shell:sh_test.bzl", "sh_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

genrule(
    name = "generate_keys",
    srcs = ["generate_keys.sh"],
    outs = [
        "server.key",
        "server.pem",
    ],
    cmd = "$(location generate_keys.sh) $(@D)",
)

proto_library(
    name = "tls_over_grpc_proto",
    srcs = ["service.proto"],
)

cc_proto_library(
    name = "tls_over_grpc_cc_proto",
    deps = [":tls_over_grpc_proto"],
)

cc_grpc_library(
    name = "tls_over_grpc_cc_grpc",
    srcs = [":tls_over_grpc_proto"],
    grpc_only = True,
    deps = [":tls_over_grpc_cc_proto"],
)

cc_library(
    name = "tls_over_grpc_service_impl",
    srcs = ["service_impl.cc"],
    hdrs = ["service_impl.h"],
    deps = [
        ":tls_over_grpc_cc_grpc",
        "@boringssl//:crypto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/log",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/strings",
    ],
)

cc_binary(
    name = "server",
    srcs = ["main.cc"],
    data = [
        ":generate_keys",
    ],
    deps = [
        ":tls_over_grpc_service_impl",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/log",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
    ],
)

cc_binary(
    name = "client",
    srcs = ["client.cc"],
    data = [
        ":generate_keys",
    ],
    deps = [
        ":tls_over_grpc_cc_grpc",
        "@boringssl//:crypto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/log",
    ],
)

sh_test(
    name = "client_server_test",
    srcs = ["client_server_test.sh"],
    data = [
        ":client",
        ":server",
    ],
    env = {
        "SERVER": "$(location :server)",
        "CLIENT": "$(location :client)",
    },
)
