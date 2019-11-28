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
        ":authorization_bearer_token_metadata",
        ":policy_metadata",
        "//oak/common:app_config",
        "//oak/common:nonce_generator",
        "//oak/proto:application_cc_grpc",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_asylo//asylo/grpc/auth:null_credentials_options",
        "@com_google_asylo//asylo/identity:init",
        "@com_google_asylo//asylo/util:logging",
    ],
)

cc_library(
    name = "sgx_application_client",
    srcs = ["sgx_application_client.cc"],
    hdrs = ["sgx_application_client.h"],
    visibility = ["//visibility:public"],
    deps = [
        ":authorization_bearer_token_metadata",
        ":policy_metadata",
        "//oak/common:app_config",
        "//oak/common:nonce_generator",
        "//oak/proto:application_cc_grpc",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_asylo//asylo/grpc/auth:grpc++_security_enclave",
        "@com_google_asylo//asylo/grpc/auth:null_credentials_options",
        # TODO: Uncomment when Asylo will release remote attestation.
        # https://github.com/project-oak/oak/issues/119
        #"@com_google_asylo//asylo/grpc/auth:sgx_remote_credentials_options",
        "@com_google_asylo//asylo/identity:enclave_assertion_authority_configs",
        "@com_google_asylo//asylo/identity:descriptions",
        "@com_google_asylo//asylo/identity:init",
        "@com_google_asylo//asylo/identity/sgx:sgx_identity_util",
        "@com_google_asylo//asylo/identity/util:sha256_hash_cc_proto",
        "@com_google_asylo//asylo/util:logging",
        "@com_google_asylo//asylo/util:status",
    ],
)

cc_library(
    name = "policy_metadata",
    srcs = ["policy_metadata.cc"],
    hdrs = ["policy_metadata.h"],
    visibility = ["//visibility:public"],
    deps = [
        "//oak/common:policy",
        "//oak/proto:policy_cc_proto",
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
        "//oak/common:policy",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/base",
        "@com_google_asylo//asylo/util:logging",
    ],
)
