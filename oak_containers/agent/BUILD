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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

exports_files(["README.md"])

rust_library(
    name = "oak_containers_agent",
    srcs = glob(
        ["src/**"],
        exclude = ["src/main.rs"],
    ),
    compile_data = [":README.md"],
    deps = [
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:http",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:opentelemetry",
        "@oak_crates_index//:opentelemetry-otlp",
        "@oak_crates_index//:opentelemetry_sdk",
        "@oak_crates_index//:procfs",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:tower",
    ],
)

rust_binary(
    name = "bin/oak_containers_agent",
    srcs = ["src/main.rs"],
    compile_data = [":README.md"],
    visibility = ["//:default_visibility"],
    deps = [
        ":oak_containers_agent",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:http",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:opentelemetry",
        "@oak_crates_index//:opentelemetry-appender-tracing",
        "@oak_crates_index//:opentelemetry-otlp",
        "@oak_crates_index//:opentelemetry_sdk",
        "@oak_crates_index//:procfs",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tower",
        "@oak_crates_index//:tracing",
        "@oak_crates_index//:tracing-subscriber",
    ],
)

alias(
    name = "agent",
    actual = ":oak_containers_agent",
)
