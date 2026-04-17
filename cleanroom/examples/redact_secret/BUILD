load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//cleanroom:wasi_binary.bzl", "wasi_binary")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "redact_secret_bin",
    srcs = ["wasm.rs"],
    deps = [
        "//cleanroom/sdk:cleanroom_sdk",
    ],
)

wasi_binary(
    name = "redact_secret_wasm",
    binary = ":redact_secret_bin",
)
