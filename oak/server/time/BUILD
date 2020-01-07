#
# Copyright 2019 The Project Oak Authors
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

load("@rules_cc//cc:defs.bzl", "cc_library", "cc_test")

package(
    default_visibility = ["//oak/server:__pkg__"],
    licenses = ["notice"],
)

cc_library(
    name = "roughtime_client",
    srcs = ["roughtime_client.cc"],
    hdrs = ["roughtime_client.h"],
    deps = [
        "//oak/common:nonce_generator",
        "@com_google_asylo//asylo/util:status",
        "@roughtime//:client",
    ],
)

test_suite(
    name = "host_tests",
    tags = ["host"],
)

cc_test(
    name = "roughtime_client_test",
    srcs = [
        "roughtime_client_test.cc",
    ],
    tags = ["host"],
    deps = [
        ":roughtime_client",
        "@gtest//:gtest_main",
    ],
)
