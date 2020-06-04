load("@build_bazel_rules_nodejs//:index.bzl", "nodejs_binary")

nodejs_binary(
    name = "client",
    data = [
        "index.js",
        "//examples/hello_world/proto:hello_world.proto",
        "@hello_world_npm//@grpc/grpc-js",
        "@hello_world_npm//@grpc/proto-loader",
    ],
    entry_point = "index.js",
)
