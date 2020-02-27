# Oak Development

## Prerequisites

We use Docker to install the base dependencies that need to exist at the system
level, e.g. the Intel SGX SDK and the Rust compiler; these steps are detailed in
[`Dockerfile`](/Dockerfile). See
https://docs.docker.com/engine/reference/builder/ for more information.

Inside Docker, we use Bazel to version, install and build dependencies and our
own code. Dependencies are listed in [`WORKSPACE`](/WORKSPACE). See
https://docs.bazel.build/versions/master/external.html for more information.

To set up your development environment, you need the following applications. For
the accurate versions required for a successful build please consult the
[`Dockerfile`](/Dockerfile).

- Docker:
  - Follow install instructions in https://docs.docker.com/install
- Bazel:
  - Follow install instructions in
    https://docs.bazel.build/versions/master/install.html
- Rust:
  - Install instructions from https://rustup.rs/:
    - `curl https://sh.rustup.rs -sSf > /tmp/rustup`
    - `less /tmp/rustup` (inspect downloaded script before running it)
    - `sh /tmp/rustup` (follow on-screen instructions -- option 1 is fine to
      start with)
    - add `source $HOME/.cargo/env` to your shell init script (e.g. `.bashrc` or
      `.zshrc`)
  - Add WebAssembly target to be able to compile to WebAssembly (see
    [Rust Platform Support](https://forge.rust-lang.org/release/platform-support.html)):
    - `rustup target add wasm32-unknown-unknown`
- Protocol Buffers:
  - Install protobuf-compiler: `apt install protobuf-compiler`

[Step by step instructions for installing Oak on Ubuntu 18.04](/INSTALL.md)
shows how to install the prerequisites starting off with a clean Ubuntu install.

Note the server runs in the Docker container but the examples run on the host
machine. This means you might be missing other dependencies like the `protoc`
protocol compiler.

## Run Example Application

The following command runs both an Oak server (as a background process) and an
Oak application client:

```bash
./scripts/docker_run ./scripts/run_example hello_world
```

This command consists of the following steps performed inside Docker:

### Build Application

The following command compiles the code for an example Oak Application from Rust
to a WebAssembly module and then serializes it into a binary application
configuration file to be loaded to the Oak Server:

```bash
./scripts/build_example hello_world
```

This binary application configuration file includes the compiled Wasm code for
the Oak Application, embedded in a serialized protocol buffer that also includes
the Application's configuration.

### Run Server

#### Run Asylo Server

The following command builds and runs an Oak Server instance that is running a
specific Oak Application (this version of the server is based on the [Asylo](https://github.com/google/asylo)
framework):

```bash
./scripts/run_server "${PWD}/bazel-client-bin/examples/hello_world/config/config.bin" -s asylo
```

#### Run Development Server

In addition to the Oak Server, we provide a "development" version of the server.
It shares the same runtime as the Docker implementation, but it's built using
clang and it's a very lightweight wrapper around a simple gRPC client. It
doesn't use Docker or any of the Asylo toolchains and it does not create an
enclave.

As such, it can be used when working on the runtime, the client code or the Node
code as it can help with enabling a faster iteration.

The following command builds and runs an Oak Development Server:

```bash
./scripts/run_server "${PWD}/bazel-client-bin/examples/hello_world/config/config.bin" -s dev
```

As this compiles using clang on your local machine, it can be easily build in
debug mode, as well as use any of the Sanitizers clang supports (e.g. asan, tsan
etc.). Details about available sanitizers can be found in the
[`.bazelrc`](/.bazelrc) file.

The following command builds and run Oak Local Server with tsan enabled. Replace
`tsan` with other configurations for different sanitisers:

```bash
bazel build --config=tsan //oak/server/dev:dev_oak_runner
```

### Run Client

The following command (run in a separate terminal) compiles the code for an
example Oak Node from Rust to a WebAssembly module, and sends it to the Oak
Server running on the same machine. It works with both Servers (Docker and Dev):

```bash
./examples/hello_world/run
```
