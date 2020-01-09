#
# Copyright 2020 The Project Oak Authors
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
load("@rules_cc//cc:defs.bzl", "cc_binary")

package(
    licenses = ["notice"],
)

cc_binary(
    name = "client",
    srcs = ["tensorflow.cc"],
    deps = [
        "//examples/tensorflow/proto:tensorflow_cc_grpc",
        "//oak/client:application_client",
        "//oak/client:manager_client",
        "//oak/common:utils",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/memory",
        "@com_google_asylo//asylo/util:logging",
    ],
)

# TODO: Create a new Bazel rule `oak_application_server_docker`, that encapsulates this logic.
# https://github.com/project-oak/oak/issues/448
