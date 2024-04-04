# Google CBOR implementation:
# https://android.googlesource.com/platform/external/libcppbor

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "libcppbor",
    srcs = glob([
        "src/**/*.cpp",
    ]),
    hdrs = glob([
        "include/**/*.h",
    ]),
    include_prefix = "libcppbor",
    deps = [
        "@boringssl//:crypto",
    ],
)
