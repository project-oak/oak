package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "stdlib",
    srcs = [
        "bsearch.c",
        "ctypes.c",
        "os.cc",
        "stdlib.c",
    ] + select({
        "//cc/tflite_micro/oak:no_sse": ["string.c"],
        "//conditions:default": glob(["string/*.S"]) + ["string/memset.cc"],
    }),
    hdrs = glob(["**/*.h"]) + [
        "strtox.c"
    ] + select({
        "//cc/tflite_micro/oak:no_sse": [],
        "//conditions:default": glob(["string/*.S"]),
    }),
    copts = ["-Icc/tflite_micro/oak/stdlib/include"],
    linkopts = [
        # Implement __clrsbdi2 to count the number of leading redundant sign bits
        "-lgcc",
    ],
)
