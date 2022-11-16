# Oak Functions Launcher

Untrusted companion app that loads the Oak Functions binary in either QEMU or
crosvm, and exposes a gRPC server for communicating with the binary.
Communicates with the binary via the `oak_channel`.

## Starting the binary

The Oak Functions binary may be loaded in crosvm via

```shell
(cd oak_functions_freestanding_bin && cargo build) \
    && RUST_LOG=debug cargo run \
    --package=oak_functions_launcher \
    -- \
    --wasm=oak_functions_launcher/key_value_lookup.wasm \
    --lookup-data=oak_functions_launcher/mock_lookup_data \
    crosvm \
    --vmm-binary=/usr/local/cargo/bin/crosvm \
    --enclave-binary=oak_functions_freestanding_bin/target/x86_64-unknown-none/debug/oak_functions_freestanding_bin
```

See also the See the task integration at `xtask/src/vm.rs`. Additional
documentation is available via
`cargo run --package=oak_functions_launcher -- --help`.

```shell
cargo build --package=oak_functions_linux_fd_bin \
    && RUST_LOG=debug cargo run \
    --package=oak_functions_launcher -- \
    --wasm=oak_functions_launcher/key_value_lookup.wasm \
    --lookup-data=oak_functions_launcher/mock_lookup_data \
    native \
    --enclave-binary=target/debug/oak_functions_linux_fd_bin
```
