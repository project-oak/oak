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

load("@rules_cc//cc:cc_library.bzl", "cc_library")
load("@rules_cc//cc:cc_test.bzl", "cc_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

# Bazel library build targets.

cc_library(
    name = "recipient_context",
    srcs = ["recipient_context.cc"],
    hdrs = ["recipient_context.h"],
    deps = [
        ":utils",
        "//proto/crypto:crypto_cc_proto",
        "@boringssl//:crypto",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "sender_context",
    srcs = ["sender_context.cc"],
    hdrs = ["sender_context.h"],
    deps = [
        ":utils",
        "@boringssl//:crypto",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "utils",
    srcs = ["utils.cc"],
    hdrs = ["utils.h"],
    deps = [
        "@boringssl//:crypto",
        "@com_google_absl//absl/base:core_headers",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
        "@com_google_absl//absl/strings:str_format",
    ],
)

# Bazel test targets.

cc_test(
    name = "recipient_context_test",
    size = "small",
    srcs = ["recipient_context_test.cc"],
    deps = [
        ":recipient_context",
        ":sender_context",
        ":utils",
        "//proto/crypto:crypto_cc_proto",
        "@boringssl//:crypto",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_googletest//:gtest_main",
    ],
)

cc_test(
    name = "sender_context_test",
    size = "small",
    srcs = ["sender_context_test.cc"],
    deps = [
        ":sender_context",
        "//cc/crypto/hpke:utils",
        "@com_google_absl//absl/status:statusor",
        "@com_google_googletest//:gtest_main",
    ],
)

cc_test(
    name = "utils_test",
    size = "small",
    srcs = ["utils_test.cc"],
    deps = [
        ":utils",
        "@boringssl//:crypto",
        "@com_google_absl//absl/status:statusor",
        "@com_google_googletest//:gtest_main",
    ],
)
