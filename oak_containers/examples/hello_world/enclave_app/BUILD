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

load("@rules_oci//oci:defs.bzl", "oci_image")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")
load("//bazel:defs.bzl", "oci_runtime_bundle")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_containers_examples_hello_world_enclave_app",
    srcs = [
        "src/app.rs",
        "src/app_service.rs",
        "src/lib.rs",
    ],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        "//oak_containers/examples/hello_world/proto:hello_world_rust_proto",
        "//oak_crypto",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

rust_test(
    name = "standalone_test",
    srcs = ["tests/standalone_test.rs"],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        ":oak_containers_examples_hello_world_enclave_app",
        "//oak_client",
        "//oak_client/tonic:oak_client_tonic",
        "//oak_containers/examples/hello_world/proto:hello_world_rust_proto",
        "//oak_crypto",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_sdk/standalone:oak_sdk_standalone",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:futures-util",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)

rust_binary(
    name = "bin/oak_containers_examples_hello_world_enclave_app",
    srcs = ["src/main.rs"],
    deps = [
        ":oak_containers_examples_hello_world_enclave_app",
        "//oak_sdk/containers:oak_sdk_containers",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:tokio",
    ],
)

pkg_tar(
    name = "tar",
    srcs = [":bin/oak_containers_examples_hello_world_enclave_app"],
    package_dir = "/usr/local/bin",
    strip_prefix = "/oak_containers/examples/hello_world/enclave_app/bin",
)

oci_image(
    name = "image",
    base = "@distroless_cc_debian12",
    entrypoint = ["/usr/local/bin/oak_containers_examples_hello_world_enclave_app"],
    tars = [":tar"],
)

oci_runtime_bundle(
    name = "bundle",
    image = ":image",
)
