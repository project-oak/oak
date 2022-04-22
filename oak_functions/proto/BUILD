#
# Copyright 2021 The Project Oak Authors
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

load("@rules_java//java:defs.bzl", "java_lite_proto_library", "java_proto_library")
load("@rules_proto//proto:defs.bzl", "proto_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "invocation_proto",
    srcs = ["invocation.proto"],
    deps = ["@com_google_protobuf//:empty_proto"],
)

java_proto_library(
    name = "invocation_java_proto",
    deps = [":invocation_proto"],
)

java_lite_proto_library(
    name = "invocation_java_proto_lite",
    deps = [":invocation_proto"],
)

proto_library(
    name = "abi_proto",
    srcs = ["abi.proto"],
    deps = ["@com_google_protobuf//:empty_proto"],
)

java_proto_library(
    name = "abi_java_proto",
    deps = [":abi_proto"],
)

java_lite_proto_library(
    name = "abi_java_proto_lite",
    deps = [":abi_proto"],
)
