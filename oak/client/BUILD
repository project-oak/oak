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

package(
    licenses = ["notice"],
)

cc_library(
    name = "manager_client",
    hdrs = ["manager_client.h"],
    visibility = ["//visibility:public"],
    deps = [
        "//oak/proto:manager_cc_grpc",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/memory",
    ],
)

cc_library(
    name = "application_client",
    hdrs = ["application_client.h"],
    visibility = ["//visibility:public"],
    deps = [
        ":policy_metadata",
        "//oak/common:app_config",
        "//oak/proto:application_cc_grpc",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_asylo//asylo/grpc/auth:null_credentials_options",
        "@com_google_asylo//asylo/identity:init",
        "@com_google_asylo//asylo/util:logging",
    ],
)

cc_library(
    name = "policy_metadata",
    srcs = ["policy_metadata.cc"],
    hdrs = ["policy_metadata.h"],
    visibility = ["//visibility:public"],
    deps = [
        "//oak/common:policy",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/base",
    ],
)
