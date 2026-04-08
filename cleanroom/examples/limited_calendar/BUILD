load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//cleanroom:wasi_binary.bzl", "wasi_binary")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "limited_calendar_bin",
    srcs = ["wasm.rs"],
    deps = [
        "//cleanroom/sdk:cleanroom_sdk",
        "@oak_crates_index//:serde_json",
    ],
)

wasi_binary(
    name = "limited_calendar_wasm",
    binary = ":limited_calendar_bin",
)
