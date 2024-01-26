load("@oak//bazel:defs.bzl", "oci_runtime_bundle")
load("@rules_oci//oci:defs.bzl", "oci_image")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

# Note: These files need to be generated using cargo outside of bazel.
# Most likely, you just want to run bazel_oci_build.sh.
filegroup(
    name = "rust_bins",
    srcs = [
        "target/oak_containers_syslogd_patched",
        "target/oak_containers_orchestrator"
    ],
)

filegroup(
    name = "files",
    srcs =
        glob(["files/**"]),

)
pkg_tar(
    name = "rust_bins_tar",
    strip_prefix = "/oak_containers_system_image/target",
    package_dir = "/usr/bin",
    srcs = [":rust_bins"],
)

pkg_tar(
    name = "files_tar",
    strip_prefix = "/oak_containers_system_image/files",
    srcs = [":files"],
)

pkg_tar(
    name = "image_tar",
    deps = [
        ":rust_bins_tar",
        ":files_tar"
    ],
)
oci_image(
    name = "oci_image",
    base = "@distroless_cc_debian12",
    entrypoint = ["/main"],
    tars = [":image_tar"],
)

oci_runtime_bundle(
    name = "runtime_bundle",
    image = ":oci_image",
)