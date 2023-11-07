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

load("@rules_java//java:defs.bzl", "java_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

java_library(
    name = "hpke",
    srcs = [
        "Hpke.java",
        "KeyPair.java",
        "RecipientContext.java",
        "SenderContext.java",
    ],
    runtime_deps = [
        "//cc/crypto/hpke/jni:libhpke-jni.so",
    ],
    deps = [
        "//java/src/main/java/com/google/oak/util",
    ],
)

java_library(
    name = "hpke_android",
    srcs = [
        "Hpke.java",
        "KeyPair.java",
        "RecipientContext.java",
        "SenderContext.java",
    ],
    constraints = ["android"],
    runtime_deps = [
        "//cc/crypto/hpke/jni:libhpke-jni.so",
    ],
    deps = [
        "//java/src/main/java/com/google/oak/util:util_android",
    ],
)
