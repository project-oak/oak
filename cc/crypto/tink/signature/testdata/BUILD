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

load("@rules_cc//cc:cc_binary.bzl", "cc_binary")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

# Export all testdata files
exports_files([
    "message",
    "public_keyset",
    "signature",
])

cc_binary(
    name = "generate_keyset_and_sign",
    srcs = ["generate_keyset_and_sign.cc"],
    deps = [
        "//cc/crypto:signing_key",
        "//cc/crypto/certificate:certificate_authority",
        "//cc/crypto/certificate:utils",
        "@com_github_tink_crypto_tink_cc//tink:configuration",
        "@com_github_tink_crypto_tink_cc//tink:keyset_handle",
        "@com_github_tink_crypto_tink_cc//tink:proto_keyset_format",
        "@com_github_tink_crypto_tink_cc//tink:public_key_sign",
        "@com_github_tink_crypto_tink_cc//tink/config:global_registry",
        "@com_github_tink_crypto_tink_cc//tink/signature:signature_config",
        "@com_github_tink_crypto_tink_cc//tink/signature:signature_key_templates",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/log:check",
        "@com_google_absl//absl/log:initialize",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings:string_view",
        "@com_google_absl//absl/time",
    ],
)
