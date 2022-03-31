# Oak Development

- [Quick Start](#quick-start)
- [Meta-Advice](#meta-advice)
- [Docker vs. Native](#docker-vs-native)
- [Prerequisites](#prerequisites)
- [Xtask](#xtask)
- [Run Example Application](#run-example-application)
  - [Build Application](#build-application)
  - [Build Oak Functions Server](#build-oak-functions-server)
  - [Run Oak Functions Server](#run-oak-functions-server)
  - [Run Example Client](#run-example-client)
- [Fuzz testing](#fuzz-testing)

## Quick Start

To build and run one of the Oak example applications under Docker, run (after
[installing Docker](Docker.md) if necessary):

```bash
./scripts/docker_pull  # retrieve cached Docker image for faster builds
./scripts/docker_run xtask --logs --scope=all run-oak-functions-examples --example-name=weather_lookup --client-variant=rust
```

This should build the Runtime, an Oak Functions Application and a client for the
Application, then run them all, with log output ending something like the
following:

```log
[21:03:26; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run ❯ background server ❯ run clients ❯ rust ❯ build ⊢    Compiling oak_functions_client v0.1.0 (/workspace/oak_functions/client/rust)
    Finished release [optimized] target(s) in 15.22sk_functions_client(bin)
OK [15s]
[21:03:42; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run ❯ background server ❯ run clients ❯ rust ❯ run ⊢     Finished release [optimized] target(s) in 0.12s
     Running `target/x86_64-unknown-linux-gnu/release/oak_functions_client '--uri=http://localhost:8080' '--request={"lat":0,"lng":0}' '--expected-response-pattern=\{"temperature_degrees_celsius":.*\}'`
{"temperature_degrees_celsius":29}
OK [1s]
[21:03:26; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run ❯ background server ❯ run clients ❯ rust } ⊢ [OK] [17s]
[21:03:26; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run ❯ background server ❯ run clients } ⊢ [OK] [17s]
[21:03:20; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run ❯ background server ⊢ (waiting)
[21:03:20; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run ❯ background server ⊢ (finished) OK
[21:03:20; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run } ⊢ [OK] [25s]
[21:03:20; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup } ⊢ [OK] [25s]
[21:03:20; E:0,O:1,R:0]: oak-functions examples } ⊢ [OK] [25s]
```

Note: `./scripts/docker_pull` and `./scripts/docker_run` will need `sudo` if not
[configured otherwise](https://docs.docker.com/engine/install/linux-postinstall/).

The remainder of this document explores what's going on under the covers here,
allowing individual stages to be built and run independently.

## VS Code Dev Container

The simplest way to get up and running with a development environment that
contains all the required tools is to use
[VS Code](https://code.visualstudio.com/) with the
[Remote-Containers](https://code.visualstudio.com/docs/remote/containers)
extension. After this is installed, and VS Code is running and pointing to the
root of the Oak repository, from a separate terminal build the Docker image, if
you haven't already:

```bash
./scripts/docker_pull
```

Then from VS Code click on the Remote-Containers button in the bottom left
corner of the status bar:

![Remote-Containers status bar](https://code.visualstudio.com/assets/docs/remote/common/remote-dev-status-bar.png)

and then select "Remote-Containers: Reopen in Container".

This should attach VS Code to an instance of the Docker container with all the
dev tools installed, and configured with most linters and Rust tools.

The Rust-Analyzer extension may prompt you to download the rust-analyzer server,
in which case allow that by clicking on "Download now" in the notification.

To test that things work correctly, open a Rust file, start typing `std::`
somewhere, and autocomplete results should start showing up. Note that it may
take a while for the `rust-analyzer` extension to go through all the local code
and build its index. Alternatively, try `xtask run-tests`.

On Linux you might have to
[post-installation steps for Linux](https://docs.docker.com/engine/install/linux-postinstall/)
and run `systemctl start docker`. If you get a `Permission denied` try to
rebuild the Docker images with `./scripts/docker_build`.

## Meta-Advice

For any open-source project, the best way of figuring out what prerequisites and
dependendencies are required is to look at the projects continuous integration
(CI) scripts and configuration.

For Oak, the CI system is currently
[Google Cloud Build](https://cloud.google.com/cloud-build), so the top-level
[`cloudbuild.yaml`](/cloudbuild.yaml) file holds the project's definitive
configuration, dependencies and build scripts.

## Docker vs. Native

The Cloudbuild setup for the project relies on a project
[`Dockerfile`](/Dockerfile) to capture precise toolchain dependencies and
versions. This also allows local use of Docker to match this build environment,
using the following wrapper scripts:

- [`scripts/docker_pull`](/scripts/docker_pull) retrieves the project's most
  recent cached Docker image(s).
- [`scripts/docker_run`](/scripts/docker_run) runs its arguments within Docker,
  so can be used as a prefix for any commands described later in this document.
- [`scripts/docker_sh`](/scripts/docker_sh) runs an interactive shell within
  Docker. This can also be used to run any commands described later in this
  document.

If you want to work on the project without using Docker, you should synchronize
your installed versions of all the tools described in the next section with the
versions installed in the [`Dockerfile`](/Dockerfile). This path is not
recommended, since it requires a lot of effort to manually install all the tool
natively on your machine and keeping them up to date to the exact same version
specified in Docker.

## xtask

`xtask` is a utility binary to perform a number of common tasks within the Oak
repository. It can be run by invoking `./scripts/xtask` from the root of the
repository, or also directly `xtask`, and it has a number of flags and
sub-commands available, which should be self-explanatory, and it also supports
flag autocompletion when invoked from inside a Docker shell.

For commands that use `cargo`, by default the `xtask` runs the command only for
the modified files and the crates affected by those changes. Use `--scope=all`
to run the command for the entire code base.

## Run Example Application

Running one of the example Oak applications will confirm that all core
prerequisites have been installed. Run one inside Docker with:

```bash
xtask --logs --scope=all run-oak-functions-examples --example-name=weather_lookup --client-variant=rust
```

That script:

- builds the Oak Functions Runtime (in Rust, built to run on the host system)
- builds a particular example, including both:
  - the Oak Application itself (Rust code that is compiled to a WebAssembly
    binary)
  - an external client (Rust code built to run on the host system)
- starts the Runtime as a background process, passing it the compiled
  WebAssembly for the Oak Functins Application (which it then runs in a
  WebAssembly engine)
- runs the external client for the Application
- closes everything down.

Those steps are broken down in the following subsections; this helps figure out
where the problem is if something goes wrong.

### Build Application

The following command compiles the code for an example Oak Application from Rust
to a WebAssembly module and then serializes it into a binary application
configuration file to be loaded to the Oak Functions Server:

```bash
xtask --logs --scope=all run-oak-functions-examples --example-name=weather_lookup --client-variant=none --run-server=false
```

This binary application configuration file includes the compiled Wasm code for
the Oak Functions Application.

### Build Oak Functions Server

The following command builds the Oak Functions Runtime server. An initial build
will take some time, but subsequent builds should be cached and so run much
faster.

```bash
xtask build-oak-functions-server-variants
```

### Run Oak Functions Server

The following command builds and runs an Oak Functions Server instance, running
a specific Oak Application (which must already have been compiled into
WebAssembly, as [described above](#build-application).

```bash
xtask --scope=all --logs run-oak-functions-examples --example-name=weather_lookup --client-variant=none
```

In the end, you should end up with an Oak server running, end with log output
something like:

```log
2022-02-23T21:14:39Z INFO - refreshing lookup data from HTTP: https://storage.googleapis.com/oak_lookup_data/lookup_data_weather_sparse_s2 with auth None
2022-02-23T21:14:39Z INFO - fetched 8507683 bytes of lookup data in 626ms
2022-02-23T21:14:40Z INFO - parsed 143548 entries of lookup data in 102ms
2022-02-23T21:14:40Z DEBUG - lookup data write lock acquisition time: 709ns
2022-02-23T21:14:40Z INFO - ThreadId(3): Starting gRPC server on [::]:8080
```

### Run Example Client

The following command (run in a separate terminal) compiles the code for the
client of an example Oak Application (as [described above](#build-application)),
and runs the client code locally.

```bash
xtask --scope=all --logs run-oak-functions-examples --example-name=weather_lookup --run-server=false --client-variant=rust
```

The client should run to completion and give output something like:

```log
[21:16:17; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run ❯ run clients ❯ rust ❯ build ⊢     Finished release [optimized] target(s) in 0.11s
OK [237ms]
[21:16:17; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run ❯ run clients ❯ rust ❯ run ⊢     Finished release [optimized] target(s) in 0.14s
     Running `target/x86_64-unknown-linux-gnu/release/oak_functions_client '--uri=http://localhost:8080' '--request={"lat":0,"lng":0}' '--expected-response-pattern=\{"temperature_degrees_celsius":.*\}'`
{"temperature_degrees_celsius":29}
OK [1s]
[21:16:17; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run ❯ run clients ❯ rust } ⊢ [OK] [2s]
[21:16:17; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run ❯ run clients } ⊢ [OK] [2s]
[21:16:17; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup ❯ run } ⊢ [OK] [2s]
[21:16:17; E:0,O:0,R:1]: oak-functions examples ❯ weather_lookup } ⊢ [OK] [2s]
[21:16:17; E:0,O:1,R:0]: oak-functions examples } ⊢ [OK] [2s]
```

## Fuzz testing

We currently have fuzz testing enabled for Oak Functions on
[OSS-Fuzz](https://github.com/google/oss-fuzz/tree/master/projects/oak). In
addition, the xtask has a command for running fuzz targets `run-fuzz-targets`.
This command runs `cargo-fuzz` with the `-O` option for optimization, and
supports all `libFuzzer` options. These options must be provided as the last
argument. For instance, the following command runs all fuzz targets with a 2
seconds timeout for each target.

```bash
xtask run-cargo-fuzz -- -max_total_time=2
```

The following lists all the `libFuzzer` options:

```bash
xtask --logs run-cargo-fuzz -- -help=1
```

Moreover, `crate-name` alone or together with `target-name` could be specified
to run all targets for a specific crate, or to run a specific target,
respectively.

```bash
xtask --logs run-cargo=fuzz --crate-name=loader --target-name=wasm_invoke -- -max_total_time=20
```
