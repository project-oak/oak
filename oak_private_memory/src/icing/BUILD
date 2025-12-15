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
load("@cxx.rs//tools/bazel:rust_cxx_bridge.bzl", "rust_cxx_bridge")
load("@rules_cc//cc:cc_library.bzl", "cc_library")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_test(
    name = "test",
    srcs = ["test.rs"],
    deps = [
        ":icing",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:tempfile",
    ],
)

rust_library(
    name = "icing",
    srcs = ["lib.rs"],
    deps = [
        ":icing_ffi_bridge",
        "//proto:sealed_memory_rust_proto",
        "//src/icing/proto:icing_rust_proto",
        "@cxx.rs//:cxx",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:prost",
    ],
)

rust_library(
    name = "icing_ffi_bridge",
    srcs = ["ffi_bridge.rs"],
    edition = "2021",
    deps = [
        ":bridge",
        ":ffi_wrapper-sys",
        "//src/icing/proto:icing_rust_proto",
        "@cxx.rs//:cxx",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:prost",
    ],
)

rust_cxx_bridge(
    name = "bridge",
    src = "ffi_bridge.rs",
    deps = [":ffi_wrapper-include"],
)

cc_library(
    name = "ffi_wrapper-sys",
    srcs = ["ffi_wrapper.cc"],
    linkstatic = True,
    deps = [
        ":bridge/include",
        ":ffi_wrapper-include",
    ],
)

cc_library(
    name = "ffi_wrapper-include",
    hdrs = ["ffi_wrapper.h"],
    deps = [
        "@cxx.rs//:core",
        "@icing",
    ],
)
