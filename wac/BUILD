cc_binary(
    name = "wac",
    srcs = [
        "wac.c",
    ],
    deps = [
        ":util",
        ":wa",
    ],
    visibility = ["//visibility:public"],
)

cc_library(
    name = "util",
    srcs = [
        "util.c",
    ],
    hdrs = [
        "util.h",
    ],
)

cc_library(
    name = "wa",
    srcs = [
        "wa.c",
        "thunks.c",
    ],
    hdrs = [
        "wa.h",
        "thunks.h",
    ],
    deps = [
        ":util",
    ],
    visibility = ["//visibility:public"],
)
