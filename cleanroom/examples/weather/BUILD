load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//cleanroom:wasi_binary.bzl", "wasi_binary")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "weather_bin",
    srcs = ["wasm.rs"],
    deps = [
        "//cleanroom/sdk:cleanroom_sdk",
    ],
)

wasi_binary(
    name = "weather_wasm",
    binary = ":weather_bin",
)
