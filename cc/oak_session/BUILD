#
# Copyright 2022 The Project Oak Authors
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

load("@rules_cc//cc:cc_binary.bzl", "cc_binary")
load("@rules_cc//cc:cc_library.bzl", "cc_library")
load("@rules_cc//cc:cc_test.bzl", "cc_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

cc_library(
    name = "oak_session_bindings",
    hdrs = ["oak_session_bindings.h"],
    deps = [
        "//cc/ffi:bytes_bindings",
        "//cc/ffi:bytes_view",
        "//cc/ffi:error_bindings",
        "//oak_session/ffi:oak_session_ffi_attestation",
        "//oak_session/ffi:oak_session_ffi_client_session",
        "//oak_session/ffi:oak_session_ffi_config",
        "//oak_session/ffi:oak_session_ffi_server_session",
        "//oak_session/ffi:oak_session_ffi_testing",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/strings:string_view",
    ],
)

cc_test(
    name = "oak_session_bindings_test",
    srcs = ["oak_session_bindings_test.cc"],
    tags = ["asan"],
    deps = [
        ":oak_session_bindings",
        "//cc/ffi:bytes_bindings",
        "//cc/ffi:bytes_view",
        "//cc/ffi:error_bindings",
        "//cc/oak_session/testing:matchers",
        "//proto/session:session_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/log",
        "@com_google_googletest//:gtest_main",
    ],
)

cc_library(
    name = "client_session",
    srcs = ["client_session.cc"],
    hdrs = ["client_session.h"],
    deps = [
        ":config",
        ":oak_session_bindings",
        "//cc/ffi:bytes_bindings",
        "//cc/ffi:bytes_view",
        "//cc/ffi:error_bindings",
        "//cc/ffi:rust_bytes",
        "//proto/attestation:verification_cc_proto",
        "//proto/session:session_cc_proto",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings:string_view",
    ],
)

cc_library(
    name = "server_session",
    srcs = ["server_session.cc"],
    hdrs = ["server_session.h"],
    deps = [
        ":config",
        ":oak_session_bindings",
        "//cc/ffi:bytes_bindings",
        "//cc/ffi:bytes_view",
        "//cc/ffi:error_bindings",
        "//cc/ffi:rust_bytes",
        "//proto/attestation:verification_cc_proto",
        "//proto/session:session_cc_proto",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings:string_view",
    ],
)

cc_test(
    name = "client_server_session_test",
    srcs = ["client_server_session_test.cc"],
    tags = ["asan"],
    deps = [
        ":client_session",
        ":server_session",
        "//cc/ffi:bytes_view",
        "//cc/ffi:rust_bytes",
        "//cc/oak_session/testing:matchers",
        "//cc/testing:protocol-buffer-matchers",
        "//proto/session:session_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/log",
        "@com_google_absl//absl/status:status_matchers",
        "@com_google_absl//absl/strings:string_view",
        "@com_google_googletest//:gtest_main",
    ],
)

cc_binary(
    name = "client_server_session_benchmark",
    testonly = True,
    srcs = ["client_server_session_benchmark.cc"],
    tags = ["asan"],
    deps = [
        ":client_session",
        ":server_session",
        "//proto/session:session_cc_proto",
        "@com_github_google_benchmark//:benchmark",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/log",
        "@com_google_absl//absl/log:check",
        "@com_google_absl//absl/status:status_matchers",
    ],
)

cc_library(
    name = "config",
    srcs = ["config.cc"],
    hdrs = ["config.h"],
    deps = [
        ":oak_session_bindings",
        "//cc/ffi:bytes_view",
        "@com_google_absl//absl/functional:any_invocable",
        "@com_google_absl//absl/log",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
        "@com_google_absl//absl/strings:string_view",
    ],
)
