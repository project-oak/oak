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

load("@rules_rust//cargo:defs.bzl", "cargo_build_script")
load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_binary(
    name = "oak_containers_syslogd",
    srcs = glob(["src/**"]),
    crate_features = ["bazel"],
    # TODO: b/335717840 - Fix systemd linker issue and remove this tag.
    tags = ["noci"],
    deps = [
        ":build",
        "//oak_containers_orchestrator:lib",
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
        "@systemd",
    ],
)

cargo_build_script(
    name = "build",
    srcs = [
        "build.rs",
    ],
    build_script_env = {
        "PROTOC": "$(execpath @com_google_protobuf//:protoc)",
        "DESCRIPTOR_PROTO_PATH": "$(location @com_google_protobuf//:descriptor_proto_srcs)",
    },
    crate_features = ["bazel"],
    data = [
        "//proto/containers:interfaces_proto",
        "//proto/crypto:crypto_proto",
        "//proto/session:messages_proto",
        "@com_google_protobuf//:descriptor_proto_srcs",
        "@com_google_protobuf//:protoc",
        "@com_google_protobuf//:well_known_type_protos",
    ],
    deps = [
        "//oak_grpc_utils",
        "//oak_proto_build_utils",
        "@oak_crates_index//:prost-build",
    ],
)
