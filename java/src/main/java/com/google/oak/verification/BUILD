#
# Copyright 2022 The Project Oak Authors
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

load("@rules_java//java:defs.bzl", "java_binary")
load("@rules_kotlin//kotlin:jvm.bzl", "kt_jvm_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

java_binary(
    name = "log_entry_verifier",
    main_class = "com.google.oak.verification.LogEntryVerifier",
    runtime_deps = [
        ":verification",
    ],
)

java_binary(
    name = "signature_verifier",
    main_class = "com.google.oak.verification.SignatureVerifier",
    runtime_deps = [
        ":verification",
    ],
)

kt_jvm_library(
    name = "verification",
    srcs = glob([
        "*.java",
        "*.kt",
    ]),
    deps = [
        "@com_google_code_gson_gson",
    ],
)
