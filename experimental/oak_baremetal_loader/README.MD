# Oak Baremetal Loader

Untrusted companion app that loads the trusted runtime in either qemu or crosvm,
and exposes gRPC server for communicating with the runtime. Communicates with
the runtime via the `oak_baremetal_channel`.

## Starting the baremetal app

The baremetal app may be loaded in qemu via

```shell
(cd experimental/oak_baremetal_app_qemu && cargo build) \
&& RUST_LOG=debug cargo run --package oak_baremetal_loader -- --mode qemu experimental/oak_baremetal_app_qemu/target/target/debug/oak_baremetal_app_qemu
```

The baremetal app may be loaded in crosvm via

```shell
(cd experimental/oak_baremetal_app_crosvm && cargo build) \
&& RUST_LOG=debug cargo run --package oak_baremetal_loader -- --mode crosvm experimental/oak_baremetal_app_crosvm/target/target/debug/oak_baremetal_app_crosvm
```
