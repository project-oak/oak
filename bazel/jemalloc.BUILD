load("@rules_foreign_cc//foreign_cc:defs.bzl", "configure_make")

package(licenses = ["notice"])

filegroup(
    name = "all_srcs",
    srcs = glob(["**"]),
)

# Check here for options used when jemalloc-sys builds it
# https://github.com/tikv/jemallocator/blob/8b886be1677d1693834b158e76780a793eb3b8db/jemalloc-sys/build.rs
configure_make(
    name = "jemalloc",
    args = ["-j$(nproc)"],
    autogen = True,
    configure_in_place = True,
    configure_options = [
        "--disable-cxx",
        "--enable-doc=no",
        "--enable-shared=no",
        "--with-jemalloc-prefix=_rjem_",
        "--with-private-namespace=_rjem_",
    ],
    lib_name = "libjemalloc",
    lib_source = ":all_srcs",
    targets = [
        "install_lib_static",
    ],
    visibility = ["//visibility:public"],
)

filegroup(
    name = "gen_dir",
    srcs = [":jemalloc"],
    output_group = "gen_dir",
    visibility = ["//visibility:public"],
)
