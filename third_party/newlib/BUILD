load("@rules_foreign_cc//foreign_cc:defs.bzl", "configure_make")

filegroup(
    name = "newlib_srcs",
    srcs = glob(["newlib-4.3.0/**"]),
)

configure_make(
    name = "newlib",
    configure_options = [
        "--target=x86_64-unknown-oak",
        "--disable-multilib",
    ],
    # We don't have a separate toolchain for `x86_64-unknown-oak`, so redirect tools to the standard
    # `x86_64-linux-gnu` ones.
    env = {
        "AR_FOR_TARGET": "x86_64-linux-gnu-ar",
        "CC_FOR_TARGET": "x86_64-linux-gnu-gcc",
        "RANLIB_FOR_TARGET": "x86_64-linux-gnu-ranlib",
    },
    lib_source = ":newlib_srcs",
    out_include_dir = "x86_64-unknown-oak/include",
    out_lib_dir = "x86_64-unknown-oak/lib",
    out_static_libs = [
        "libm.a",
        "libc.a",
        "liboak.a",
    ],
    visibility = ["//visibility:public"],
)
