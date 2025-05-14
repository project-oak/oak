load("@rules_foreign_cc//foreign_cc:configure.bzl", "configure_make")

licenses(["notice"])  # Apache v2.0

package(
    default_visibility = ["//visibility:public"],
)

# We need to label this for configure_make.
filegroup(
    name = "all",
    srcs = glob(["**"]),
)

configure_make(
    name = "icu",
    args = select({
        # AR is overridden to be libtool by rules_foreign_cc. It does not support ar style arguments
        # like "r". We need to prevent the icu make rules from adding unsupported parameters by
        # forcing ARFLAGS to keep the rules_foreign_cc value in this parameter
        "@platforms//os:macos": [
            "ARFLAGS=\"-static -o\"",
            "MAKE=gnumake",
            "-j$(nproc)",
        ],
        "//conditions:default": [
            "-j$(nproc)",
        ],
    }),
    configure_command = "source/configure",
    configure_in_place = True,
    configure_options = [
        "--enable-option-checking",
        "--enable-static",
        "--enable-tools",  # needed to build data
        "--disable-shared",
        "--disable-dyload",
        "--disable-extras",
        "--disable-plugins",
        "--disable-tests",
        "--disable-samples",
        "--with-data-packaging=static",
    ],
    env = {
        "CXXFLAGS": "-fPIC",  # For JNI
        "CFLAGS": "-fPIC",  # For JNI
    },
    lib_source = "@icu//:all",
    out_static_libs = [
        "libicui18n.a",
        "libicuio.a",
        "libicuuc.a",
        "libicudata.a",
    ],
)

cc_library(
    name = "common",
    deps = [
        "icu",
    ],
)

cc_library(
    name = "headers",
    deps = [
        "icu",
    ],
)

cc_library(
    name = "unicode",
    deps = [
        "icu",
    ],
)

exports_files([
    "icu4c/LICENSE",
])
