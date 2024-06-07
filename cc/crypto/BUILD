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
    name = "client_encryptor",
    srcs = ["client_encryptor.cc"],
    hdrs = ["client_encryptor.h"],
    deps = [
        ":common",
        "//cc/crypto/hpke:sender_context",
        "//cc/crypto/hpke:utils",
        "//proto/crypto:crypto_cc_proto",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "server_encryptor",
    srcs = ["server_encryptor.cc"],
    hdrs = ["server_encryptor.h"],
    deps = [
        ":common",
        ":encryption_key",
        "//cc/crypto/hpke:recipient_context",
        "//cc/crypto/hpke:utils",
        "//proto/crypto:crypto_cc_proto",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "encryption_key",
    srcs = ["encryption_key.cc"],
    hdrs = ["encryption_key.h"],
    deps = [
        ":common",
        "//cc/crypto/hpke:recipient_context",
        "//proto/crypto:crypto_cc_proto",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "common",
    hdrs = ["common.h"],
    deps = [
        "@com_google_absl//absl/strings",
    ],
)

cc_library(
    name = "signing_key",
    hdrs = ["signing_key.h"],
    deps = [
        ":common",
        "//proto/crypto:crypto_cc_proto",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

cc_test(
    name = "encryptor_test",
    size = "small",
    srcs = ["encryptor_test.cc"],
    deps = [
        ":client_encryptor",
        ":common",
        ":encryption_key",
        ":server_encryptor",
        "//cc/crypto/hpke:recipient_context",
        "@com_google_absl//absl/strings",
        "@com_google_googletest//:gtest_main",
    ],
)
