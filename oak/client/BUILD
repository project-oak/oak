cc_binary(
    name = "client",
    srcs = ["oak_client.cc"],
    deps = [
        "@com_github_gflags_gflags//:gflags_nothreads",
        "@com_google_asylo//asylo/util:logging",
        "//oak:oak_proto_cc",
        "//oak:oak_server_grpc_proto",
        "@com_github_grpc_grpc//:grpc++",
    ],
)
