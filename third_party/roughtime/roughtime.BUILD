package(
    default_visibility = ["//visibility:public"],
)

cc_library(
    name = "roughtime_logging",
    hdrs = ["logging.h"],
    copts = ["-Wno-sometimes-uninitialized"],
    deps = ["@com_google_protobuf//:protobuf"],
)

cc_library(
    name = "protocol",
    srcs = ["protocol.cc"],
    hdrs = ["protocol.h"],
    deps = [
        ":roughtime_logging",
        "@boringssl//:crypto",
    ],
)

cc_library(
    name = "client",
    srcs = ["client.cc"],
    hdrs = ["client.h"],
    copts = ["-Wno-sometimes-uninitialized"],
    deps = [
        ":protocol",
        ":roughtime_logging",
    ],
)
