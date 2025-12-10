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

cc_library(
    name = "oak_session_tls",
    srcs = ["oak_session_tls.cc"],
    hdrs = ["oak_session_tls.h"],
    deps = [
        "@boringssl//:crypto",
        "@boringssl//:ssl",
        "@com_google_absl//absl/log",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
    ],
)

cc_library(
    name = "util",
    srcs = ["util.cc"],
    hdrs = ["util.h"],
    deps = [
        ":oak_session_tls",
        "@boringssl//:crypto",
        "@boringssl//:ssl",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_test(
    name = "oak_session_tls_test",
    srcs = ["oak_session_tls_test.cc"],
    data = ["//oak_session/tls/testing:test_keys"],
    deps = [
        ":oak_session_tls",
        ":util",
        "@boringssl//:crypto",
        "@boringssl//:ssl",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:status_matchers",
        "@com_google_absl//absl/status:statusor",
        "@com_google_googletest//:gtest_main",
    ],
)
