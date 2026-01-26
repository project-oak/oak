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

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_binary(
    name = "oak_containers_syslogd",
    srcs = glob(["src/**"]),
    deps = [
        "//oak_containers/orchestrator",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:bitflags",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:opentelemetry",
        "@oak_crates_index//:opentelemetry-otlp",
        "@oak_crates_index//:opentelemetry_sdk",
        "@oak_crates_index//:signal-hook",
        "@oak_crates_index//:signal-hook-tokio",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

alias(
    name = "syslogd",
    actual = ":oak_containers_syslogd",
)
