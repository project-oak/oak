<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Oak Functions Containers Launcher

Tools for packaging the Oak Functions Containers app as an OCI runtime bundle.

In order to bring the launcher up with the Oak Functions Trusted Application on
Oak Containers, do the following:

Build all the necessary components of Oak Containers. A script in the
`oak_functions_containers_container` folder can help generate the container
image. However, to generate all necessary components, there is also a rule in
the just file:

```console
just all_oak_functions_containers_binaries
```

Build the WASM module to be used, for example:

```console
just all_wasm_test_crates
```

Bring up the Oak Functions Launcher, for example to run it with the test lookup
Wasm module:

```console
$ artifacts/oak_functions_containers_launcher \
    --vmm-binary=$(which qemu-system-x86_64) \
    --stage0-binary=artifacts/stage0_bin \
    --kernel=artifacts/oak_containers_kernel \
    --initrd=artifacts/stage1.cpio \
    --system-image=artifacts/oak_containers_system_image.tar.xz \
    --container-bundle=artifacts/oak_functions_containers_app_bundle.tar \
    --ramdrive-size=1000000 \
    --memory-size=10G \
    --wasm=target/wasm32-unknown-unknown/release/key_value_lookup.wasm \
    --lookup-data=oak_functions_launcher/mock_lookup_data
```

To test the example lookup service while the Oak Functions Launcher is running,
execute the client in a separate shell:

```console
bazel run //cc/client:cli -- --address=127.0.0.1:8080 --request=test_key
```
