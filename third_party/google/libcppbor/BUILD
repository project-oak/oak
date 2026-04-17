# Google CBOR implementation:
# https://android.googlesource.com/platform/external/libcppbor

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "libcppbor",
    srcs = glob(
        ["src/**/*.cpp"],
        allow_empty = True,
    ),
    hdrs = glob(
        ["include/**/*.h"],
        allow_empty = True,
    ),
    include_prefix = "libcppbor",
    deps = [
        "@boringssl//:crypto",
    ],
)
