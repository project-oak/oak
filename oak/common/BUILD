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

load("@rules_cc//cc:defs.bzl", "cc_library", "cc_test")

package(
    licenses = ["notice"],
)

cc_library(
    name = "hmac",
    srcs = ["hmac.cc"],
    hdrs = ["hmac.h"],
    visibility = ["//visibility:public"],
    deps = [
        "//third_party/asylo:statusor",
        "@boringssl//:crypto",
        "@com_google_absl//absl/status",
    ],
)

cc_test(
    name = "hmac_test",
    srcs = ["hmac_test.cc"],
    deps = [
        ":hmac",
        "@gtest//:gtest_main",
    ],
)

cc_library(
    name = "label",
    srcs = ["label.cc"],
    hdrs = ["label.h"],
    visibility = ["//visibility:public"],
    deps = [
        "//oak_abi/proto:label_cc_proto",
        "@com_google_absl//absl/base",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "nonce_generator",
    srcs = [],
    hdrs = ["nonce_generator.h"],
    visibility = ["//visibility:public"],
    deps = [
        "@com_google_absl//absl/base",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "utils",
    srcs = ["utils.cc"],
    hdrs = ["utils.h"],
    visibility = ["//visibility:public"],
    deps = [
        "@com_github_google_glog//:glog",
    ],
)
