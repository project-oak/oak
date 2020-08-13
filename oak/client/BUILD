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
    licenses = ["notice"],
)

cc_library(
    name = "application_client",
    hdrs = ["application_client.h"],
    visibility = ["//visibility:public"],
    deps = [
        ":authorization_bearer_token_metadata",
        ":label_metadata",
        "//oak/common:hmac",
        "//oak/common:nonce_generator",
        "//oak/common:utils",
        "@com_github_grpc_grpc//:grpc++",
    ],
)

cc_library(
    name = "label_metadata",
    srcs = ["label_metadata.cc"],
    hdrs = ["label_metadata.h"],
    visibility = ["//visibility:public"],
    deps = [
        "//oak/common:label",
        "//oak_services/proto:label_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/base",
    ],
)

cc_library(
    name = "authorization_bearer_token_metadata",
    srcs = ["authorization_bearer_token_metadata.cc"],
    hdrs = ["authorization_bearer_token_metadata.h"],
    visibility = ["//visibility:public"],
    deps = [
        "//oak/common:label",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/base",
    ],
)
