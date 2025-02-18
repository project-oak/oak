# Common Rust FFI support for Oak
# This crate defines some common useful types that other Rust FFI implementations can use.
# The corresponding Rust types are in oak_ffi

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

cc_library(
    name = "bytes_bindings",
    srcs = ["bytes_bindings.cc"],
    hdrs = ["bytes_bindings.h"],
    deps = [
        "//oak_ffi:oak_ffi_bytes",
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
