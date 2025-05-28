"""Create rules for nixpkgs-provided pkgs"""

load("@io_tweag_rules_nixpkgs//nixpkgs:nixpkgs.bzl", "nixpkgs_package")

def setup_nix_kernels():
    nixpkgs_package(
        name = "nix_vanilla_linux_kernel",
        build_file_content = "exports_files([\"bzImage\"])",
        nix_file = "@//oak_containers/kernel:vanilla-kernel.nix",
        nix_file_deps = [
            "@//oak_containers/kernel:kernel-common.nix",
            "@//oak_containers/kernel:kernel_version.txt",
            "@//oak_containers/kernel/configs/6.12.25:minimal.config",
        ],
        repository = "@nixpkgs",
    )

    nixpkgs_package(
        name = "nix_linux_kernel",
        build_file_content = "exports_files([\"bzImage\"])",
        nix_file = "@//oak_containers/kernel:kernel.nix",
        nix_file_deps = [
            "@//oak_containers/kernel:kernel-common.nix",
            "@//oak_containers/kernel:kernel_version.txt",
            "@//oak_containers/kernel/configs/6.12.25:minimal.config",
            "@//oak_containers/kernel/patches:virtio-dma.patch",
            "@//oak_containers/kernel/patches:tdx-probe-roms.patch",
            "@//oak_containers/kernel/patches:rtmr-enable.patch",
        ],
        repository = "@nixpkgs",
    )
