load("@oak//bazel:defs.bzl", "oci_runtime_bundle")
load("@rules_oci//oci:defs.bzl", "oci_image", "oci_tarball", "oci_push")

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

# This just turns the filegroup into a tar that oci_image can reference.
pkg_tar(
    name = "rust_bins_tar",
    strip_prefix = "/oak_containers_system_image/target",
    package_dir = "/usr/bin",
    srcs = [":rust_bins"],
)

# Not currently working because the base image isn't getting generated in the correct format
oci_image(
    name = "oci_image",
    entrypoint = ["/main"],
    base = "@oak_containers_sysimage_base",
    tars = [":rust_bins_tar"]
)

# Spits out the actual tarball that we want
oci_runtime_bundle(
    name = "runtime_bundle",
    image = ":oci_image",
)


# Just for experimentation: show that the oci_image build rule works on the distroless base
# The distroless version is missing base OS configuration, and won't work in an Oak container.
oci_image(
    name = "distroless_image",
    entrypoint = ["/main"],
    base = "@distroless_cc_debian12",
    tars = [":rust_bins_tar"]
)

# Spits out a tar for the distroless image, just so we can see that the Oak files are in the right place.
# The distroless version is missing base OS configuration, and won't work in an Oak container.
oci_runtime_bundle(
    name = "distroless_runtime_bundle",
    image = ":distroless_image",
)

## Rules for updating the base image

# This gets created by runing build-base.sh
filegroup(
    name = "base_image_tar",
    srcs = [
        "target/oak_container_sysimage_oci_image_base_bundle.tar"
    ]
)

# This (hopefully) creates an OCI image use the base image tar above
oci_image(
    name = "oak_containers_sysimage_base",
    os = "linux",
    architecture = "amd64",
    tars =[":base_image_tar"]
)

# This should push the base image to the Google artifact repository
oci_push(
    image = ":oak_containers_sysimage_base",
    name = "push_base",
    repository = "europe-west2-docker.pkg.dev/oak-ci/oak-containers-sysimage-base/oak-containers-sysimage-base",
    remote_tags = ["latest"],
)
