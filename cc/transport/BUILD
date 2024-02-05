#
# Copyright 2023 The Project Oak Authors
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
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "transport",
    hdrs = ["transport.h"],
    deps = [
        "//proto/crypto:crypto_cc_proto",
        "//proto/session:messages_cc_proto",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "grpc_streaming_transport",
    srcs = ["grpc_streaming_transport.cc"],
    hdrs = ["grpc_streaming_transport.h"],
    deps = [
        ":transport",
        "//proto/crypto:crypto_cc_proto",
        "//proto/session:messages_cc_proto",
        "//proto/session:service_streaming_cc_grpc",
        "//proto/session:service_streaming_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/log",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_test(
    name = "grpc_streaming_transport_test",
    srcs = ["grpc_streaming_transport_test.cc"],
    deps = [
        ":grpc_streaming_transport",
        "//proto/crypto:crypto_cc_proto",
        "//proto/session:messages_cc_proto",
        "//proto/session:service_streaming_cc_grpc",
        "//proto/session:service_streaming_cc_proto",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/log",
        "@com_google_absl//absl/log:absl_check",
        "@com_google_absl//absl/status",
        "@com_google_googletest//:gtest_main",
    ],
)
