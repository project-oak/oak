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
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:prost",
        "@pm_crates//:cxx",
    ],
)

rust_library(
    name = "icing_ffi_bridge",
    srcs = ["ffi_bridge.rs"],
    deps = [
        ":bridge",
        ":ffi_wrapper-sys",
        "//src/icing/proto:icing_rust_proto",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:prost",
        "@pm_crates//:cxx",
    ],
)

genrule(
    name = "bridge/generated",
    srcs = ["ffi_bridge.rs"],
    outs = [
        "ffi_bridge.rs.h",
        "ffi_bridge.rs.cc",
    ],
    cmd = "$(location @cxx.rs//:codegen) $(location ffi_bridge.rs) -o $(location ffi_bridge.rs.h) -o $(location ffi_bridge.rs.cc)",
    tools = ["@cxx.rs//:codegen"],
)

cc_library(
    name = "bridge",
    srcs = ["ffi_bridge.rs.cc"],
    linkstatic = True,
    deps = [
        ":bridge/include",
        ":ffi_wrapper-include",
    ],
)

cc_library(
    name = "bridge/include",
    hdrs = ["ffi_bridge.rs.h"],
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
