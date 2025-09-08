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
    name = "verification-ffi",
    srcs = ["verification-ffi.cc"],
    hdrs = ["verification-ffi.h"],
    deps = [
        ":verification_utils",
        "//cc/ffi:bytes_view",
        "//cc/ffi:cxx_string",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/strings:string_view",
    ],
)

cc_library(
    name = "verification_utils",
    srcs = ["verification_utils.cc"],
    hdrs = ["verification_utils.h"],
    deps = [
        "//cc/ffi:bytes_view",
        "//cc/ffi:cxx_string",
        "//cc/utils/status",
        "@com_github_tink_crypto_tink_cc//tink:keyset_handle",
        "@com_github_tink_crypto_tink_cc//tink:proto_keyset_format",
        "@com_github_tink_crypto_tink_cc//tink:public_key_verify",
        "@com_github_tink_crypto_tink_cc//tink/config:global_registry",
        "@com_github_tink_crypto_tink_cc//tink/signature:signature_config",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings:string_view",
    ],
)

cc_test(
    name = "verification_utils_test",
    size = "small",
    srcs = ["verification_utils_test.cc"],
    deps = [
        ":verification_utils",
        "@com_github_tink_crypto_tink_cc//tink:configuration",
        "@com_github_tink_crypto_tink_cc//tink:keyset_handle",
        "@com_github_tink_crypto_tink_cc//tink:proto_keyset_format",
        "@com_github_tink_crypto_tink_cc//tink:public_key_sign",
        "@com_github_tink_crypto_tink_cc//tink:public_key_verify",
        "@com_github_tink_crypto_tink_cc//tink/config:global_registry",
        "@com_github_tink_crypto_tink_cc//tink/signature:signature_config",
        "@com_github_tink_crypto_tink_cc//tink/signature:signature_key_templates",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:status_matchers",
        "@com_google_absl//absl/status:statusor",
        "@com_google_googletest//:gtest_main",
    ],
)

cc_library(
    name = "signature-ffi",
    testonly = True,
    srcs = ["signature-ffi.cc"],
    hdrs = ["signature-ffi.h"],
    deps = [
        ":signature_utils",
        "//cc/ffi:bytes_view",
        "//cc/ffi:cxx_string",
        "@com_google_absl//absl/status:statusor",
    ],
)

cc_library(
    name = "signature_utils",
    # Currently only supported for tests. If this is ever intended for non-test use,
    # testcases should be added.
    testonly = True,
    srcs = ["signature_utils.cc"],
    hdrs = ["signature_utils.h"],
    deps = [
        "//cc/utils/status",
        "@com_github_tink_crypto_tink_cc//tink:keyset_handle",
        "@com_github_tink_crypto_tink_cc//tink:proto_keyset_format",
        "@com_github_tink_crypto_tink_cc//tink:public_key_sign",
        "@com_github_tink_crypto_tink_cc//tink/config:global_registry",
        "@com_github_tink_crypto_tink_cc//tink/signature:signature_config",
        "@com_github_tink_crypto_tink_cc//tink/signature:signature_key_templates",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings:string_view",
    ],
)
