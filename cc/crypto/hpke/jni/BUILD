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
load("@rules_cc//cc:cc_library.bzl", "cc_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

cc_library(
    name = "hpke-jni-lib",
    srcs = [
        "context_jni.cc",
        "hpke_jni.cc",
        "jni_helper.cc",
        "keypair_jni.cc",
    ],
    hdrs = [
        "com_google_oak_crypto_hpke_Hpke.h",
        "com_google_oak_crypto_hpke_KeyPair.h",
        "com_google_oak_crypto_hpke_RecipientContext.h",
        "com_google_oak_crypto_hpke_SenderContext.h",
        "jni_helper.h",
    ],
    deps = [
        "//cc/crypto/hpke:recipient_context",
        "//cc/crypto/hpke:sender_context",
        "//cc/crypto/hpke:utils",
        "@bazel_tools//tools/jdk:jni",
        "@com_google_absl//absl/status:statusor",
    ],
    alwayslink = 1,
)

cc_binary(
    name = "libhpke-jni.so",
    linkshared = 1,
    linkstatic = 1,
    deps = [":hpke-jni-lib"],
)
