<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Oak Functions Containers Launcher

Tools for packaging the Oak Functions Containers app as an OCI runtime bundle.

In order to bring the launcher up with the Oak Functions Trusted Application on
Oak Containers, do the following:

Build all the necessary components of Oak Containers. A script in the ```oak_functions_containers_container``` folder can help generate the container image. However, to generate all necessary components, there is also a rule in the just file:
```
just all_oak_functions_containers_binaries
```

Bring up the Oak Functions Launcher with the Trusted App:
```
cargo run -- \
    --system-image ../oak_containers_system_image/target/image.tar.xz \
    --container-bundle ../oak_functions_containers_container/target/oak_container_example_oci_filesystem_bundle.tar \
    --vmm-binary `which qemu-system-x86_64` \
    --stage0-binary ../stage0_bin/target/x86_64-unknown-none/release/stage0_bin \
    --kernel ../oak_containers_kernel/target/bzImage \
    --initrd ../target/stage1.cpio \
    --ramdrive-size 5000000 \
    --memory-size 10G
```
