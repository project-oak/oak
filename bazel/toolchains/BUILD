load("@rules_cc//cc:defs.bzl", "cc_toolchain")
load(":cc_toolchains.bzl", "cc_x86_64_unknown_none_toolchain_config")

package(licenses = ["notice"])

filegroup(name = "empty")

cc_x86_64_unknown_none_toolchain_config(
    name = "cc_x86_64_unknown_none_toolchain_config",
)

cc_toolchain(
    name = "cc_x86_64_unknown_none_toolchain",
    all_files = ":empty",
    compiler_files = ":empty",
    dwp_files = ":empty",
    linker_files = ":empty",
    objcopy_files = ":empty",
    strip_files = ":empty",
    supports_param_files = 0,
    toolchain_config = "cc_x86_64_unknown_none_toolchain_config",
)

toolchain(
    name = "x86_64_unknown_none_toolchain",
    exec_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:linux",
    ],
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
    ],
    toolchain = "cc_x86_64_unknown_none_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)
