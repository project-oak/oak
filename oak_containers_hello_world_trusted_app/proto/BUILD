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
load("@rules_cc//cc:defs.bzl", "cc_proto_library")
load("@rules_proto//proto:defs.bzl", "proto_library")

package(
    default_visibility = [
        "//cc/containers/hello_world_trusted_app:__subpackages__",
        "//oak_containers_hello_world_trusted_app:__subpackages__",
    ],
    licenses = ["notice"],
)

proto_library(
    name = "interface_proto",
    srcs = ["interface.proto"],
    deps = [
        "//proto/crypto:crypto_proto",
    ],
)

cc_proto_library(
    name = "interface_cc_proto",
    deps = [":interface_proto"],
)

cc_grpc_library(
    name = "interface_cc_grpc",
    srcs = [":interface_proto"],
    grpc_only = True,
    deps = [":interface_cc_proto"],
)
