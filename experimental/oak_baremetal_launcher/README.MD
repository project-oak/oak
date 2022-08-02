# Oak Baremetal Loader

Untrusted companion app that loads the trusted runtime in either QEMU or crosvm,
and exposes a gRPC server for communicating with the runtime. Communicates with
the runtime via the `oak_baremetal_channel`.

## Starting the baremetal app

The baremetal app may be loaded in QEMU via

```shell
(cd experimental/oak_baremetal_app_qemu && cargo build) \
&& RUST_LOG=debug cargo run --package oak_baremetal_launcher -- \
--wasm experimental/oak_baremetal_launcher/key_value_lookup.wasm \
--lookup-data experimental/oak_baremetal_launcher/mock_lookup_data \
qemu \
--vmm-binary /usr/bin/qemu-system-x86_64 \
--app-binary experimental/oak_baremetal_app_qemu/target/x86_64-unknown-none/debug/oak_baremetal_app_qemu
```

The baremetal app may be loaded in crosvm via

```shell
(cd experimental/oak_baremetal_app_crosvm && cargo build) \
&& RUST_LOG=debug cargo run --package oak_baremetal_launcher -- \
--wasm experimental/oak_baremetal_launcher/key_value_lookup.wasm \
--lookup-data experimental/oak_baremetal_launcher/mock_lookup_data \
crosvm \
--vmm-binary /usr/local/cargo/bin/crosvm \
--app-binary experimental/oak_baremetal_app_crosvm/target/x86_64-unknown-none/debug/oak_baremetal_app_crosvm
```

See also the See the task integration at `xtask/src/vm.rs`. Additionally a documentation is available via `cargo run --package oak_baremetal_launcher -- --help`.


```shell
cargo build --package oak_functions_loader_linux_native \
&& RUST_LOG=debug cargo run --package oak_baremetal_launcher -- \
--wasm experimental/oak_baremetal_launcher/key_value_lookup.wasm \
--lookup-data experimental/oak_baremetal_launcher/mock_lookup_data \
native \
--app-binary target/debug/oak_functions_loader_linux_native
```
