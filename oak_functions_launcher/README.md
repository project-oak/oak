# Oak Functions Launcher

The Oak Functions Launcher loads the Oak Functions enclave binary and exposes a
gRPC server for communicating with the binary via the
[Oak Channel](../oak_channel).

## Launching the Oak Functions enclave binary

First, if running "rootless" Docker, set the permission to access the KVM kernel
module by either (i) `sudo setfacl -m u:${USER}:rw /dev/kvm` on the host, or by
(ii) adding the user to the KVM group.

Then, run the following from within the
[Oak Developer Docker Container](../docs/development.md#docker-helper-scripts):

To launch tests of the Oak Functions Launcher with `xtask`:

```shell
xtask run-launcher-test
```

Additional documentation is available via
`cargo run --package=oak_functions_launcher -- --help`.

To launch the Oak Functions binary directly as a child process:

```shell
cargo build --package=oak_functions_linux_fd_bin \
    && RUST_LOG=debug cargo run \
    --package=oak_functions_launcher -- \
    --wasm=oak_functions_launcher/key_value_lookup.wasm \
    --lookup-data=oak_functions_launcher/mock_lookup_data \
    native \
    --enclave-binary=target/debug/oak_functions_linux_fd_bin
```

Output:

```shell
[2023-01-12T16:38:04Z INFO  oak_functions_launcher] read Wasm file from disk oak_functions_launcher/key_value_lookup.wasm (1728193 bytes)
INFO: Connecting to the launcher via the file descriptor: 11
```
