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

load("@io_bazel_rules_docker//container:container.bzl", "container_image")
load("@rules_cc//cc:defs.bzl", "cc_binary", "cc_library")

package(
    default_visibility = [
        "//examples:__subpackages__",
        "//oak/server:__subpackages__",
    ],
    licenses = ["notice"],
)

cc_library(
    name = "oak_loader",
    srcs = [
        "oak_loader.cc",
    ],
    hdrs = [
        "oak_loader.h",
    ],
    deps = [
        "//oak/common:logging",
        "//oak/proto:application_cc_grpc",
        "//oak/server:oak_runtime",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/strings",
    ],
)

cc_binary(
    name = "oak_runner",
    srcs = ["oak_runner_main.cc"],
    deps = [
        ":oak_loader",
        "//oak/common:app_config",
        "//oak/common:logging",
        "//oak/common:utils",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/synchronization",
        "@com_google_absl//absl/time",
    ],
)

container_image(
    name = "oak_docker",
    base = "@cc_image//image",
    files = [
        "oak_runner",
        "//examples/certs/docker:ca.pem",
        "//examples/certs/docker:docker.key",
        "//examples/certs/docker:docker.pem",
    ],
    ports = [
        "8080/tcp",  # Oak Application gRPC port.
    ],
    repository = "gcr.io/oak-ci",
)
