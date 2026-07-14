#
# Copyright 2026 The Project Oak Authors
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

load("@rules_kotlin//kotlin:android.bzl", "kt_android_library")
load("@rules_kotlin//kotlin:jvm.bzl", "kt_jvm_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

kt_jvm_library(
    name = "oak_session_tls",
    srcs = [
        "OakSessionTls.kt",
        "OakSessionTlsContext.kt",
        "OakSessionTlsException.kt",
        "OakSessionTlsInitializer.kt",
    ],
    target_compatible_with = ["@platforms//os:linux"],
)

kt_jvm_library(
    name = "cert_util",
    srcs = ["CertUtil.kt"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":oak_session_tls",
        "@maven//:org_bouncycastle_bcpkix_jdk18on",
        "@maven//:org_bouncycastle_bcprov_jdk18on",
    ],
)

kt_android_library(
    name = "oak_session_tls_android",
    srcs = [
        "OakSessionTls.kt",
        "OakSessionTlsContext.kt",
        "OakSessionTlsException.kt",
        "OakSessionTlsInitializer.kt",
    ],
    manifest = "AndroidManifest.xml",
)

kt_android_library(
    name = "cert_util_android",
    srcs = ["CertUtil.kt"],
    deps = [
        ":oak_session_tls_android",
        "@maven//:org_bouncycastle_bcpkix_jdk18on",
        "@maven//:org_bouncycastle_bcprov_jdk18on",
    ],
)
