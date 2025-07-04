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

load("@rules_cc//cc:cc_binary.bzl", "cc_binary")
load("@rules_cc//cc:cc_library.bzl", "cc_library")
load("@rules_cc//cc:cc_test.bzl", "cc_test")
load("@rules_oci//oci:defs.bzl", "oci_image")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("//bazel:defs.bzl", "oci_runtime_bundle")

package(licenses = ["notice"])

cc_library(
    name = "app_service",
    srcs = ["app_service.cc"],
    hdrs = ["app_service.h"],
    deps = [
        "//cc/containers/sdk:orchestrator_client",
        "//cc/crypto:common",
        "//cc/oak_session:oak_session_bindings",
        "//cc/oak_session:server_session",
        "//cc/utils/status",
        "//oak_containers/examples/hello_world/proto:hello_world_cc_grpc",
        "//oak_containers/examples/hello_world/proto:hello_world_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/strings",
    ],
)

cc_binary(
    name = "main",
    srcs = ["main.cc"],
    deps = [
        ":app_service",
        "//cc/containers/sdk:orchestrator_client",
        "@com_github_grpc_grpc//:grpc++",
        "@com_github_grpc_grpc//:grpc++_reflection",
        "@com_google_absl//absl/log:check",
        "@com_google_absl//absl/log:initialize",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
    ],
)

cc_test(
    name = "standalone_test",
    srcs = ["standalone_test.cc"],
    deps = [
        ":app_service",
        "//cc/containers/sdk/standalone:oak_standalone",
        "//cc/oak_session:client_session",
        "//oak_containers/examples/hello_world/proto:hello_world_cc_grpc",
        "@com_google_absl//absl/log:check",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:status_matchers",
        "@com_google_googletest//:gtest_main",
    ],
)

cc_binary(
    name = "standalone_benchmark",
    testonly = True,
    srcs = ["standalone_benchmark.cc"],
    deps = [
        ":app_service",
        "//cc/attestation/verification:insecure_attestation_verifier",
        "//cc/containers/sdk/standalone:oak_standalone",
        "//cc/oak_session:client_session",
        "//oak_containers/examples/hello_world/proto:hello_world_cc_grpc",
        "@com_github_google_benchmark//:benchmark",
        "@com_google_absl//absl/log:check",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:status_matchers",
    ],
)

pkg_tar(
    name = "tar",
    srcs = [":main"],
    package_dir = "/usr/local/bin",
)

oci_image(
    name = "image",
    base = "@distroless_cc_debian12",
    entrypoint = ["/usr/local/bin/main"],
    tars = [":tar"],
)

oci_runtime_bundle(
    name = "bundle",
    image = ":image",
    visibility = [
        "//oak_containers/examples/hello_world/host_app:__subpackages__",
    ],
)
