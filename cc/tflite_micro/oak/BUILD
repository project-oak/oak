load(
    ":build_def.bzl",
    "oak_copts",
)

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "debug_log",
    srcs = [
        "debug_log.cc",
    ],
    copts = oak_copts(),
    alwayslink = 1,
)

cc_library(
    name = "hdrs",
    hdrs = ["tflite_micro.h"],
)

# --define no_sse=1 to build tflite w/o streaming SIMD instructions.
# It would also use non-optimized stdlib {str|mem}xxx functions.
config_setting(
    name = "no_sse",
    values = {
        "define": "no_sse=1",
    },
)

# --define no_opt=1 to disable compiler optimizations (-O0)
# rather than taking the default full optimizaiton (-O3)
config_setting(
    name = "no_opt",
    values = {
        "define": "no_opt=1",
    },
)