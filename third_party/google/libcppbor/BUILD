# Google CBOR implementation:
# https://android.googlesource.com/platform/external/libcppbor

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "libcppbor",
    hdrs = glob([
        "include/**/*.h",
    ]),
    srcs = glob([
        "src/**/*.cpp",
    ]),
    include_prefix = "libcppbor",
    deps = [
        "@boringssl//:crypto",
    ],
)
