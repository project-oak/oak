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
bazel test oak_functions_launcher/...
```

Additional documentation is available via:

```shell
bazel run oak_functions_launcher -- --help
```

To launch the Oak Functions binary with the default support binaries, use the
`just` command, providing a wasm target to run and a lookup data file.

```shell
# These aren't built automatically every time, to make iterating faster.
just oak-functions-launcher-artifacts

just run-oak-functions-launcher \
    oak_functions_launcher/key_value_lookup \
    oak_functions_launcher/mock_lookup_data
```

(See the just command for details)

Output:

```shell
[2023-02-27T16:54:15Z INFO  oak_functions_launcher] read Wasm file from disk oak_functions_launcher/key_value_lookup.wasm (1.65MiB)
[2023-02-27T16:54:15Z INFO  oak_functions_launcher] service initialized: InitializeResponse { public_key_info: Some(PublicKeyInfo { public_key: [], attestation: [] }) }
[2023-02-27T16:54:15Z INFO  oak_functions_launcher] obtained public key (0 bytes)
```
