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

load("@com_google_protobuf//bazel:cc_proto_library.bzl", "cc_proto_library")
load("@com_google_protobuf//bazel:java_proto_library.bzl", "java_proto_library")
load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")
load("@com_google_protobuf//bazel:py_proto_library.bzl", "py_proto_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

exports_files([
    "endorsement.proto",
    "verification_material.proto",
])

proto_library(
    name = "verification_material_proto",
    srcs = ["verification_material.proto"],
)

cc_proto_library(
    name = "verification_material_cc_proto",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [":verification_material_proto"],
)

java_proto_library(
    name = "verification_material_java_proto",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [":verification_material_proto"],
)

py_proto_library(
    name = "verification_material_py_pb2",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [":verification_material_proto"],
)

proto_library(
    name = "endorsement_proto",
    srcs = ["endorsement.proto"],
    deps = [":verification_material_proto"],
)

cc_proto_library(
    name = "endorsement_cc_proto",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [":endorsement_proto"],
)

java_proto_library(
    name = "endorsement_java_proto",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [":endorsement_proto"],
)

py_proto_library(
    name = "endorsement_py_pb2",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [":endorsement_proto"],
)
