"""Module extension for Nix packages.

The bzlmod variant of nixpkgs setups don't allow dependencies to build targets
that depend on the nixpkgs (the repositories are "root-only"). This module
extension allows us to setup the nixpkgs repository and then define packages
within it that we can depend on.
"""

load("@rules_nixpkgs_core//:nixpkgs.bzl", "nixpkgs_git_repository", "nixpkgs_package")

def _nix_kernels_impl(ctx):
    for mod in ctx.modules:
        if mod.name != "oak":
            fail("nix_kernels extension can only be used by the 'oak' module, but was requested by '{}'".format(mod.name))

        for tag in mod.tags.repository:
            # Setup nixpkgs repository
            nixpkgs_git_repository(
                name = "nixpkgs",
                remote = tag.remote,
                revision = tag.revision,
                sha256 = tag.sha256,
            )

    # Setup vanilla kernel
    nixpkgs_package(
        name = "nix_vanilla_linux_kernel",
        build_file_content = "exports_files([\"bzImage\"])",
        nix_file = "//oak_containers/kernel:vanilla-kernel.nix",
        nix_file_deps = [
            "//oak_containers/kernel:kernel-common.nix",
            "//oak_containers/kernel:kernel_version.txt",
            "//oak_containers/kernel/configs/6.12.90:minimal.config",
        ],
        repository = "@nixpkgs",
    )

    # Setup linux kernel with patches
    nixpkgs_package(
        name = "nix_linux_kernel",
        build_file_content = "exports_files([\"bzImage\"])",
        nix_file = "//oak_containers/kernel:kernel.nix",
        nix_file_deps = [
            "//oak_containers/kernel:kernel-common.nix",
            "//oak_containers/kernel:kernel_version.txt",
            "//oak_containers/kernel/configs/6.12.90:minimal.config",
            "//oak_containers/kernel/patches:virtio-dma.patch",
            "//oak_containers/kernel/patches:tdx-probe-roms.patch",
            "//oak_containers/kernel/patches:rtmr-enable.patch",
        ],
        repository = "@nixpkgs",
    )

repository_tag = tag_class(
    attrs = {
        "remote": attr.string(mandatory = True),
        "revision": attr.string(mandatory = True),
        "sha256": attr.string(),
    },
)

nix_kernels = module_extension(
    implementation = _nix_kernels_impl,
    tag_classes = {
        "repository": repository_tag,
    },
)
