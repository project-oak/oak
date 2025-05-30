# Common Rust FFI support for Oak
# This crate defines some common useful types that other Rust FFI implementations can use.
# The corresponding Rust types are in oak_ffi

load("@rules_cc//cc:cc_library.bzl", "cc_library")
load("@rules_cc//cc:cc_test.bzl", "cc_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

cc_library(
    name = "bytes_bindings",
    hdrs = [
        "bytes_bindings.h",
    ],
    deps = [
        "//oak_ffi:oak_ffi_bytes",
        "@com_google_absl//absl/strings:string_view",
    ],
)

cc_library(
    name = "bytes_view",
    hdrs = ["bytes_view.h"],
    deps = [
        "@com_google_absl//absl/strings:string_view",
    ],
)

cc_library(
    name = "error_bindings",
    srcs = ["error_bindings.cc"],
    hdrs = ["error_bindings.h"],
    deps = [
        ":bytes_bindings",
        "//oak_ffi:oak_ffi_error",
        "@com_google_absl//absl/status",
    ],
)

cc_library(
    name = "rust_bytes",
    hdrs = ["rust_bytes.h"],
    deps = [
        ":bytes_bindings",
        "@com_google_absl//absl/strings:string_view",
    ],
)

cc_library(
    name = "cxx_string",
    srcs = ["cxx_string.cc"],
    hdrs = ["cxx_string.h"],
)

cc_test(
    name = "bytes_view_test",
    srcs = ["bytes_view_test.cc"],
    deps = [
        ":bytes_view",
        # Without this dependency, we see linker errors, with allocator-related symbols not being present.
        # If we uncomment this dependency, everything builds and links. But what is this actually adding
        # that's not present in :bytes_bindings?
        #":error_bindings",
        "@com_google_googletest//:gtest_main",
    ],
)

cc_library(
    name = "absl_status",
    srcs = ["absl_status.cc"],
    hdrs = ["absl_status.h"],
    deps = [
        ":bytes_view",
        "@com_google_absl//absl/status",
    ],
)
