#
# Copyright 2025 The Project Oak Authors
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

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
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
