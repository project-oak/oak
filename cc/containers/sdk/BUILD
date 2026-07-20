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

load("@rules_cc//cc:cc_library.bzl", "cc_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

cc_library(
    name = "common",
    hdrs = ["common.h"],
    target_compatible_with = ["@platforms//os:linux"],
)

cc_library(
    name = "encryption_key_handle",
    srcs = ["encryption_key_handle.cc"],
    hdrs = ["encryption_key_handle.h"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":orchestrator_crypto_client",
        "//cc/crypto:encryption_key",
        "//cc/crypto/hpke:recipient_context",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "orchestrator_client",
    srcs = ["orchestrator_client.cc"],
    hdrs = ["orchestrator_client.h"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":common",
        "//proto/containers:interfaces_cc_grpc",
        "//proto/containers:interfaces_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "orchestrator_crypto_client",
    srcs = ["orchestrator_crypto_client.cc"],
    hdrs = ["orchestrator_crypto_client.h"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":common",
        "//proto/containers:orchestrator_crypto_cc_grpc",
        "//proto/containers:orchestrator_crypto_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "signing_key_handle",
    srcs = ["signing_key_handle.cc"],
    hdrs = ["signing_key_handle.h"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":orchestrator_crypto_client",
        "//cc/crypto:signing_key",
        "//proto/crypto:crypto_cc_proto",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)
