#
# Copyright 2024 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test", "rust_test_suite")
load("//bazel:defs.bzl", "any_platform")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

DEPS = [
    "//micro_rpc",
    "//oak_functions_abi",
    "//oak_proto_rust",
    "//oak_proto_rust/micro_rpc",
    "@oak_crates_index//:anyhow",
    "@oak_crates_index//:log",
    "@oak_crates_index//:prost",
    "@oak_crates_index//:rand_core",
    "@oak_crates_index//:spinning_top",
    "@oak_crates_index//:wasmi",
]

UNRESTRICTED_DEPS = DEPS + [
    "@oak_crates_index//:parking_lot",
    "@oak_crates_index//:wasmtime",
]

rust_library(
    name = "lib",
    srcs = glob(["src/**/*.rs"]),
    # The features are inverted on purpose; this means the "default" package
    # will not have sensitive logging enabled.
    crate_features = ["deny_sensitive_logging"],
    crate_name = "oak_functions_service",
    target_compatible_with = any_platform([
        "//:aarch64-apple-setting",
        "//:x86_64-none-setting",
        "//:x86_64-linux-setting",  # Needed to run unit tests.
    ]),
    deps = DEPS,
)

rust_library(
    name = "lib_insecure",
    srcs = glob(["src/**/*.rs"]),
    crate_features = ["allow_sensitive_logging"],
    crate_name = "oak_functions_service",
    target_compatible_with = any_platform([
        "//:x86_64-none-setting",
        "//:x86_64-linux-setting",  # Needed to run unit tests.
    ]),
    deps = DEPS,
)

rust_library(
    name = "lib_unrestricted",
    srcs = glob(["src/**/*.rs"]),
    crate_features = [
        "deny_sensitive_logging",
        "std",
        "wasmtime",
    ],
    crate_name = "oak_functions_service",
    deps = UNRESTRICTED_DEPS,
)

rust_library(
    name = "lib_insecure_unrestricted",
    srcs = glob(["src/**/*.rs"]),
    crate_features = [
        "allow_sensitive_logging",
        "std",
        "wasmtime",
    ],
    crate_name = "oak_functions_service",
    deps = UNRESTRICTED_DEPS,
)

rust_test(
    name = "lib_test",
    crate = ":lib",
    data = ["//oak_functions/examples/echo"],
    deps = [
        "//oak_functions_test_utils",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:prost",
    ],
)

rust_test(
    name = "lib_unrestricted_test",
    crate = ":lib_unrestricted",
    data = ["//oak_functions/examples/echo"],
    deps = [
        "//oak_functions_test_utils",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:prost",
    ],
)

rust_test(
    name = "lib_insecure_test",
    crate = ":lib_insecure",
    data = ["//oak_functions/examples/echo"],
    deps = [
        "//oak_functions_test_utils",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:prost",
    ],
)

rust_test(
    name = "lib_insecure_unrestricted_test",
    crate = ":lib_insecure_unrestricted",
    data = ["//oak_functions/examples/echo"],
    deps = [
        "//oak_functions_test_utils",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:prost",
    ],
)

rust_test_suite(
    name = "benches",
    srcs = ["benches/wasm_benchmark.rs"],
    data = [
        "//oak_functions/examples/echo",
        "//oak_functions/examples/key_value_lookup",
        "//oak_functions_test_module",
    ],
    proc_macro_deps = [
        "@oak_crates_index//:criterion-macro",
    ],
    shared_srcs = ["benches/perf.rs"],
    deps = [
        ":lib_unrestricted",
        "//micro_rpc",
        "//oak_file_utils",
        "//oak_functions_abi",
        "//oak_functions_test_utils",
        "//oak_proto_rust",
        "//oak_proto_rust/micro_rpc",
        "@oak_crates_index//:criterion",
        "@oak_crates_index//:hashbrown",
        "@oak_crates_index//:pprof",
        "@oak_crates_index//:wasmi",
        "@oak_crates_index//:wasmtime",
    ],
)
