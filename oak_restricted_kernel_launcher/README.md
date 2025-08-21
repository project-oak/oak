# oak_restricted_kernel_launcher

Simple launcher used to launch an instance of the restricted kernel in a VM.

Documentation is available via:

```shell
bazel run oak_restricted_kernel_launcher -- --help
```

The instructions below for building the required dependencies and running an app
using this launcher are provided on a best effort basis.

First the dependencies used to run launch an instance of the restricted kernel
must be built.

(instructions gained from inspecting xtask, may change in the future)

The easiest way to run the launcher is to use the included just command, which
will use the default support dependencies, so you only need to provide the
target of an enclave app to run.

```shell

# These aren't built automatically every time, to make iterating faster.
just oak-rk-launcher-artifacts

just run-oak-functions-launcher \
    oak_functions_launcher/key_value_lookup \
    oak_functions_launcher/mock_lookup_data
```

(See the just command for details)
