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

To launch integration tests of the Oak Functions Launcher:

```shell
cargo test --package=oak_functions_launcher
```

Additional documentation is available via:

```shell
cargo run --package=oak_functions_launcher -- --help
```
