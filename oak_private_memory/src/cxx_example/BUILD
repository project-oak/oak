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
load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    licenses = ["notice"],
)

rust_binary(
    name = "demo",
    srcs = ["main.rs"],
    edition = "2021",
    deps = [
        ":bridge",
        ":mystring-sys",
        "@cxx.rs//:cxx",
    ],
)

rust_cxx_bridge(
    name = "bridge",
    src = "main.rs",
    deps = [":mystring-include"],
)

cc_library(
    name = "mystring-sys",
    srcs = ["mystring.cc"],
    linkstatic = True,
    deps = [
        ":bridge/include",
        ":mystring-include",
    ],
)

cc_library(
    name = "mystring-include",
    hdrs = ["mystring.h"],
    deps = ["@cxx.rs//:core"],
)
