load("@io_bazel_rules_go//go:def.bzl", "go_binary")

go_binary(
    name = "hello_world",
    srcs = [
        "hello_world.go",
    ],
    # Exclude cgo.
    pure = "on",
    goos = "js",
    goarch = "wasm",
)
