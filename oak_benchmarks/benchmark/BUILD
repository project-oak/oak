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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "benchmark",
    srcs = [
        "src/cpu/mod.rs",
        "src/lib.rs",
        "src/memory/mod.rs",
        "src/service.rs",
    ],
    crate_features = [],
    deps = [
        "//oak_benchmarks/proto:service",
    ],
)

rust_library(
    name = "benchmark_std",
    srcs = [
        "src/cpu/mod.rs",
        "src/lib.rs",
        "src/memory/mod.rs",
        "src/service.rs",
        "src/tests.rs",
    ],
    crate_features = ["std"],
    crate_name = "benchmark",
    deps = [
        "//oak_benchmarks/proto:service",
    ],
)

rust_test(
    name = "benchmark_test",
    crate = ":benchmark_std",
)
