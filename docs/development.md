# Oak Development

- [Quick Start](#quick-start)
- [Meta-Advice](#meta-advice)
- [Docker vs. Native](#docker-vs-native)
- [Prerequisites](#prerequisites)
- [Run Example Application](#run-example-application)
  - [Build Application](#build-application)
  - [Build Runtime Server](#build-runtime-server)
  - [Run Runtime Server](#run-runtime-server)
  - [Run Example Client](#run-example-client)

## Quick Start

To build and run one of the Oak example applications under Docker, run:

```bash
./scripts/docker_pull  # retrieve cached Docker image for faster builds
./scripts/docker_run ./scripts/runner run-examples --example-name=hello_world
```

This should build the Runtime, an Oak Application and a client for the
Application, then run them all, with log output ending something like the
following:

```log
2020-05-11 17:24:18,770 INFO  [oak_runtime::runtime] stopping runtime instance
2020-05-11 17:24:18,770 DEBUG [oak_runtime::runtime] waking waiters on NodeId(0) handle 11172775277784258633 => Channel 0 WRITE
2020-05-11 17:24:18,770 INFO  [oak_runtime::runtime] Runtime instance dropped
2020-05-11 17:24:18,770 DEBUG [oak_runtime::runtime::channel] last writer for channel 0 gone, wake waiters
2020-05-11 17:24:18,770 DEBUG [oak_runtime::runtime::channel] dropping Channel object Channel { id=0, #readers=0, #writers=0, label=Label { confidentiality_tags: [], integrity_tags: [] } }
```

The remainder of this document explores what's going on under the covers here,
allowing individual stages to be built and run independently, and allowing
builds that don't have to rely on a Docker environment.

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
versions installed in the [`Dockerfile`](/Dockerfile).

## Prerequisites

The key prerequisites for the project are:

- **Rust**: The [Rust toolchain](https://www.rust-lang.org/tools/install) and
  ancillary tools are required for building the project's source. Note that we
  also [require](https://github.com/project-oak/oak/issues/969) a nightly build
  of Rust; check the [`Dockerfile`](/Dockerfile) for the specific version.
  - Follow install instructions from https://rustup.rs/, roughly:
    - `curl https://sh.rustup.rs -sSf > /tmp/rustup`
    - `less /tmp/rustup` (inspect downloaded script before running it)
    - `sh /tmp/rustup` (follow on-screen instructions -- option 1 is fine to
      start with)
    - add `source $HOME/.cargo/env` to your shell init script (e.g. `.bashrc` or
      `.zshrc`)
  - Add the WebAssembly target to add support for producing WebAssembly binaries
    (see
    [Rust Platform Support](https://forge.rust-lang.org/release/platform-support.html)):
    `rustup target add wasm32-unknown-unknown`
  - Install additional tools (e.g. `rustfmt` and `clippy`) as indicated by the
    [`Dockerfile`](/Dockerfile) contents.
- **Support for [musl](https://musl.libc.org/)** (on Linux): The
  [Oak Runtime](/docs/concepts.md#oak-runtime) is built as a
  [fully static binary](https://doc.rust-lang.org/edition-guide/rust-2018/platform-and-target-support/musl-support-for-fully-static-binaries.html),
  on Linux, which requires:
  - the Rust `x86_64-unknown-linux-musl` target
    (`rustup target add x86_64-unknown-linux-musl`)
  - the [musl-tools](https://packages.debian.org/search?keywords=musl-tools)
    package to be installed.
- **Bazel**: The [Bazel build system](https://bazel.build) is used for building
  C++ code and managing its dependencies. These dependencies are listed in the
  top-level [`WORKSPACE`](/WORKSPACE) file; see the
  [Bazel docs](https://docs.bazel.build/versions/master/external.html) for more
  information. Follow the
  [Bazel install instructions](https://docs.bazel.build/versions/master/install.html).
- **Protocol Buffers**: Install the appropriate version of the protobuf compiler
  from the
  [releases page](https://github.com/protocolbuffers/protobuf/releases).

These prerequisites cover what's needed to build the core codebase, and to run
the top-level build scripts described in the sections below.

A full development environment for the project also includes various extra
tools, for example for linting and synchronizing documentation. As ever, the
[`Dockerfile`](/Dockerfile) holds the details, but the scripts under
[`scripts/`](/scripts) also indicate what's needed for different steps.

## Run Example Application

Running one of the example Oak applications will confirm that all core
prerequisites have been installed. Run one inside Docker with:

```bash
./scripts/docker_run ./scripts/runner run-examples --example-name=hello_world
```

or, if all prerequisites are available on the local system, outside of Docker:

```bash
./scripts/runner run-examples --example-name=hello_world
```

That script:

- builds the Oak Runtime (a combination of C++ and Rust, built to run on the
  host system)
- builds a particular example, including both:
  - the Oak Application itself (Rust code that is compiled to a WebAssembly
    binary)
  - an external client (C++ code built to run on the host system)
- starts the Runtime as a background process, passing it the compiled
  WebAssembly for the Oak Application (which it then runs in a WebAssembly
  engine)
- runs the external client for the Application
- closes everything down.

Those steps are broken down in the following subsections; this helps figure out
where the problem is if something goes wrong.

### Build Application

The following command compiles the code for an example Oak Application from Rust
to a WebAssembly module and then serializes it into a binary application
configuration file to be loaded to the Oak Server:

```bash
./scripts/runner run-examples --run-server=false --run-clients=false --example-name=hello_world
```

This binary application configuration file includes the compiled Wasm code for
the Oak Application, embedded in a serialized protocol buffer that also includes
the Application's configuration.

The `scripts/build_example` script also builds (using Bazel) the corresponding
client code for the Oak Application, to produce a binary that runs on the host
system. Because the client talks to the Oak Application over gRPC, the client
can be written in any language that supports gRPC; most of the example clients
are written in C++, but there are clients in
[Go](/examples/translator/client/translator.go) and
[Rust](/examples/authentication/client/src/main.rs).

### Build Runtime Server

The following command builds the Oak Runtime server. An initial build will take
some time, but subsequent builds should be cached and so run much faster.

```bash
./scripts/runner build-server
```

### Run Runtime Server

The following command builds and runs an Oak Server instance, running a specific
Oak Application (which must already have been compiled into WebAssembly and
built into a serialized configuration, as [described above](#build-application).

```bash
./scripts/runner run-examples --run-clients=false --example-name=hello_world
```

In the end, you should end up with an Oak server running, end with log output
something like:

```log
2020-05-11 10:14:14,952 INFO  [sdk/rust/oak/src/lib.rs:460] starting event loop
2020-05-11 10:14:14,952 DEBUG [oak_runtime::runtime] NodeId(2): wait_on_channels: channels not ready, parking thread Thread { id: ThreadId(4), name: Some("log.LogNode(2)") }
2020-05-11 10:14:14,955 DEBUG [oak_runtime::node::wasm] hello_world.WasmNode-oak_main(1): wait_on_channels(1114152, 1)
2020-05-11 10:14:14,955 DEBUG [oak_runtime::runtime] NodeId(1): wait_on_channels: channels not ready, parking thread Thread { id: ThreadId(3), name: Some("hello_world.WasmNode-oak_main(1)") }
```

### Run Example Client

The following command (run in a separate terminal) compiles the code for the
client of an example Oak Application (as [described above](#build-application)),
and runs the client code locally.

```bash
./scripts/runner run-examples --run-server=false --logs --example-name=hello_world
```

The `-s none` option indicates that the script expects to find an
already-running Oak Runtime (from the previous section), rather than launching
an Oak Runtime instance of its own.

The client should run to completion and give output something like:

```log
I0511 10:15:29.539814 244858 hello_world.cc:66] Connecting to Oak Application: localhost:8080
I0511 10:15:29.541366 244858 hello_world.cc:36] Request: WORLD
I0511 10:15:29.558292 244858 hello_world.cc:43] Response: HELLO WORLD!
I0511 10:15:29.558353 244858 hello_world.cc:36] Request: MONDO
I0511 10:15:29.568802 244858 hello_world.cc:43] Response: HELLO MONDO!
I0511 10:15:29.568862 244858 hello_world.cc:36] Request: 世界
I0511 10:15:29.578845 244858 hello_world.cc:43] Response: HELLO 世界!
I0511 10:15:29.578902 244858 hello_world.cc:36] Request: MONDE
I0511 10:15:29.585346 244858 hello_world.cc:43] Response: HELLO MONDE!
I0511 10:15:29.585389 244858 hello_world.cc:50] Request: WORLDS
I0511 10:15:29.591434 244858 hello_world.cc:57] Response: HELLO WORLDS!
I0511 10:15:29.593106 244858 hello_world.cc:57] Response: HELLO AGAIN WORLDS!
```
