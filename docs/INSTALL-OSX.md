# Developing With OS X

Developing under an OS X environment is not supported.

However, this document covers some tips that might help if you want to try OS X
development of Oak.

## Prerequisites

First, [install Bazel](https://docs.bazel.build/versions/master/install.html);
Bazel handles local copies of toolchains and other C++ code that Oak depends on.

Next, setup a gcloud account and initialize local credentials with
`gcloud auth login`. This is needed because some of the Oak dependencies are
retrieved from a Google Cloud Docker repository.

Set up a local Rust install of the nightly Rust compiler. To ensure that the
version and ancillary tools are in sync with those used by our continuous
integration system, check the specific details in the project
[`Dockerfile`](/Dockerfile):

<!-- prettier-ignore-start -->
[embedmd]:# (../Dockerfile bash /^# Install rustup/ /^ +rustfmt/)
```bash
# Install rustup.
ARG rustup_dir=/usr/local/cargo
ENV RUSTUP_HOME ${rustup_dir}
ENV CARGO_HOME ${rustup_dir}
ENV PATH "${rustup_dir}/bin:${PATH}"
RUN curl --location https://sh.rustup.rs > /tmp/rustup \
  && sh /tmp/rustup -y --default-toolchain=none \
  && chmod a+rwx ${rustup_dir} \
  && rustup --version

# Install Rust toolchain.
# We currently need the nightly version in order to be able to compile some of the examples.
# See https://rust-lang.github.io/rustup-components-history/ for how to pick a version that supports
# the appropriate set of components.
# Make sure to update WORKSPACE too, e.g. when updating nightly version
ARG rust_version=nightly-2020-04-17
RUN rustup toolchain install ${rust_version} \
  && rustup default ${rust_version}

# Install WebAssembly target for Rust.
RUN rustup target add wasm32-unknown-unknown

# Install musl target for Rust (for statically linked binaries).
RUN rustup target add x86_64-unknown-linux-musl

# Install rustfmt, clippy, and the Rust Language Server.
RUN rustup component add \
  clippy \
  rls \
  rust-analysis \
  rust-src \
  rustfmt
```
<!-- prettier-ignore-end -->

## Building and Running

The Oak Runtime and its dependencies are built with the following script:

```bash
./scripts/build_server
```

Build a particular example, say `hello_world`, with:

```bash
./scripts/build_example -e hello_world
```

Note that the Runtime server requires a particular Oak Application to run, and
so relies on the previous section.

```bash
./scripts/run_server -e hello_world
```

In a separate terminal, run an example client that connects to the Oak Runtime
with the following (the `-s none` option indicates that no new Runtime server is
needed, so the client will connect to the already-running server of the previous
step):

```bash
./scripts/run_example -s none -e hello_world
```

## Codebase Tools

The Oak codebase also makes use of several linting tools. To run these, and
their wrapper scripts (e.g. [`scripts/format`](/scripts/format) and
[`scripts/check_formatting`](/scripts/check_formatting)), the OS X versions of
the tools will need to be installed. Check the top-level
[`Dockerfile`](/Dockerfile) for the set of required tools.
