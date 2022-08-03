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

load("@rules_java//java:defs.bzl", "java_library", "java_test")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

java_library(
    name = "client",
    srcs = glob(["src/main/java/com/google/oak/client/*.java"]),
    deps = [":util"],
)

java_library(
    name = "util",
    srcs = glob(["src/main/java/com/google/oak/util/*.java"]),
    deps = [],
)

java_test(
    name = "client_test",
    srcs = glob(["src/test/java/com/google/oak/client/*.java"]),
    test_class = "com.google.oak.client.OakClientTest",
    deps = [
        ":client",
        ":util",
    ],
)

java_test(
    name = "util_test",
    srcs = glob(["src/test/java/com/google/oak/util/*.java"]),
    test_class = "com.google.oak.util.ResultTest",
    deps = [
        ":util",
    ],
)
