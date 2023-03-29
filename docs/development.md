# Oak Development

## Quick Start

Development of Oak is only supported within a Docker environment on Linux, which
guarantees that all the developers are using the same exact version of all the
compilers and build tools, and that this is also in sync with what is used by
the Continous Integration (CI) system.

This is also necessary (though not by itself sufficient) to enable building Oak
binaries in a detereministic and reproducible way, which in turn allows Oak to
be [transparently released](https://github.com/project-oak/transparent-release).

Mac and Windows development is not supported.

If you want to work on the project without using Docker, you should synchronize
your installed versions of all the tools described in the next sections with the
versions installed in the [`Dockerfile`](/Dockerfile). This path is not
recommended, since it requires a lot of effort to manually install all the tool
natively on your machine and keeping them up to date to the exact same version
specified in Docker.

The Docker image is manually built from the checked-in
[Dockerfile](/Dockerfile), and pushed to `gcr.io/oak-ci/oak`, from which other
developers can also access it.

### Rootless Docker

The Docker image and other scripts in this repository expect that the Docker
daemon is running as the local user instead of root.

In order to run Docker without root privileges, follow the guide at
https://docs.docker.com/engine/security/rootless/ .

Below is a quick summary of the relevant steps:

1. If you have an existing version of Docker running as root, uninstall that
   first:

   ```bash
   sudo systemctl disable --now docker.service docker.socket
   sudo apt remove docker-ce docker-engine docker-runc docker-containerd
   ```

1. Install `uidmap`:

   ```bash
   sudo apt install uidmap
   ```

1. Add a range of subids for the current user:

   ```bash
   sudo usermod --add-subuids 500000-565535 --add-subgids 500000-565535 $USER
   ```

1. Download the install script for rootless Docker, and run it as the current
   user:

   ```bash
   curl -fSSL https://get.docker.com/rootless > $HOME/rootless
   sh $HOME/rootless
   ```

1. Add the generated environment variables to your shell:

   ```bash
   export PATH=$HOME/bin:$PATH
   export DOCKER_HOST=unix://$XDG_RUNTIME_DIR/docker.sock
   ```

   **As an alternative** to setting the `DOCKER_HOST` environment variable, it
   is possible to instead run the following command to set the Docker context:

   ```bash
   docker context use rootless
   ```

   In either case, running the following command should show the current status:

   ```console
   $ docker context ls
   NAME        DESCRIPTION                               DOCKER ENDPOINT                       KUBERNETES ENDPOINT   ORCHESTRATOR
   default *   Current DOCKER_HOST based configuration   unix:///run/user/152101/docker.sock                         swarm
   rootless    Rootless mode                             unix:///run/user/152101/docker.sock
   Warning: DOCKER_HOST environment variable overrides the active context. To use a context, either set the global --context flag, or unset DOCKER_HOST environment variable.
   ```

   This should show either that the default context is selected and is using the
   user-local docker endpoint from the `DOCKER_HOST` variable, or that the
   `rootless` context is selected.

1. Test whether everything works correctly:

   ```bash
   docker run hello-world
   ```

If you rely on VS Code remote / dev container support, that should also keep
working, but you need to make sure that your VS Code instance sees the update
environment variables so that it connects to the correct Docker host socket. The
simplest way of doing this is to invoke `code` from a shell with the updated
environment variables.

### Pull the latest Oak development image

To build and run one of the Oak example applications under Docker, run the
following commands:

```bash
./scripts/docker_pull  # Retrieve cached Docker development image, locked from the current commit.
./scripts/docker_run xtask --logs --scope=all run-oak-functions-examples --example-name=weather_lookup --client-variant=rust
```

This should build the Oak Functions Runtime, an Oak Functions Application and a
client for the Application, then run them all, with log output ending something
like the following:

```log
[19:12:46 ✓:0,✗:0,⠇:1] ││││││└─▶OK 1s
[19:12:46 ✓:0,✗:0,⠇:1] │││││└[rust]─▶[OK] 64s
[19:12:46 ✓:0,✗:0,⠇:1] ││││└[run clients]─▶[OK] 64s
[19:12:48 ✓:0,✗:0,⠇:1] ││││ (waiting for completion)
[19:12:48 ✓:0,✗:0,⠇:1] │││└[background server]─▶OK
[19:12:48 ✓:0,✗:0,⠇:1] ││└[run]─▶[OK] 72s
[19:12:48 ✓:0,✗:0,⠇:1] │└[weather_lookup]─▶[OK] 270s
[19:12:48 ✓:1,✗:0,⠇:0] └[oak-functions examples]─▶[OK] 270s
```

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
dependendencies are required is to look at the projects CI scripts and
configuration.

For Oak, the CI system is [GitHub Actions](https://docs.github.com/en/actions),
so the [`ci.yaml`](/.github/workflows/ci.yaml) file holds the project's
definitive configuration, dependencies and build scripts.

## Docker Helper Scripts

- [`scripts/docker_pull`](/scripts/docker_pull) retrieves the Docker image
  corresponding to the current commit, as specified in
  [`scripts/common`](/scripts/common).
- [`scripts/docker_build`](/scripts/docker_build) builds the Docker image from
  the current [`Dockerfile`](/Dockerfile) and updates the image id in
  [`scripts/common`](/scripts/common).
- [`scripts/docker_push`](/scripts/docker_push) pushes the Docker image to the
  Docker repository, and updates the image digest in
  [`scripts/common`](/scripts/common), so that CI tools and other developers can
  use it.
- [`scripts/docker_run`](/scripts/docker_run) runs its arguments within the
  Docker development image, so can be used as a prefix for any commands
  described later in this document.
- [`scripts/docker_sh`](/scripts/docker_sh) runs an interactive shell within the
  Docker development image. This can also be used to run any commands described
  later in this document.

## Nix

Support for [Nix](https://nixos.org/) for local development is experimental.

### Quick Installation

Install Nix in single-user mode
([source](https://nixos.wiki/wiki/Nix_Installation_Guide#Stable_Nix)):

```console
sudo install -d -m755 -o $(id -u) -g $(id -g) /nix
curl --location https://releases.nixos.org/nix/nix-2.14.1/install > /tmp/install_nix \
  && echo '565974057264f0536f600c68d59395927cd73e9fc5a60f33c1906e8f7bc33fcf  /tmp/install_nix' > /tmp/install_nix.sha256 \
  && sha256sum --check /tmp/install_nix.sha256 \
  && sh /tmp/install_nix
```

Enable support for [Nix Flakes](https://nixos.wiki/wiki/Flakes) by adding the
following to your `~/.config/nix/nix.conf` (create it if necessary)
([source](https://nixos.wiki/wiki/Flakes#Permanent)):

```text
experimental-features = nix-command flakes
```

## Quick Usage Guide

Get a Nix development shell:

```console
nix develop
```

This will drop you into a subshell in which a completely deterministic
environment (e.g. compilers, dev tools) is available, based on the configuration
described in [`flake.nix`](/flake.nix).

Note that this may take a while (up to 10 minutes) on the first run, since Nix
has to download all the dependencies from scratch. It will be almost instant in
future invocations, unless dependencies are changed again.

Some things to try:

- See where tools are installed from within the dev shell:

  ```console
  $ which rustc
  /nix/store/mrf09022h38ykgsfb50xcv3q1izf5gac-rust-default-1.69.0-nightly-2023-02-15/bin/rustc
  ```

- Add a new tool to the list, and see it reflected in the dev shell:

  - enter the default dev shell:

    ```console
    nix develop
    ```

  - check `ponysay` is not installed on the host or the default dev shell:

    ```console
    $ ponysay hello
    zsh: command not found: ponysay
    ```

  - add `ponysay` to the list of packages in [`flake.nix`](/flake.nix), e.g.
    next to `protobuf`
  - exit the previous dev shell (e.g. via `Ctrl-D`)
  - re-create a new dev shell:

    ```console
    nix develop
    ```

  - try the `ponysay` command again from within the dev shell:

    ```console
    $ ponysay hello
    _______________________
    < hello                 >
    -----------------------
    ```

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
- starts the Oak Functions Runtime as a background process, passing it the
  compiled WebAssembly for the Oak Functins Application (which it then runs in a
  WebAssembly engine)
- runs the external client for the Application
- closes everything down.

Those steps are broken down in the following subsections; this helps figure out
where the problem is if something goes wrong.

### Build Application

The following command compiles the code for an example Oak Functions Application
from Rust to a WebAssembly module to be loaded by the Oak Functions Server:

```bash
xtask --logs --scope=all run-oak-functions-examples --example-name=weather_lookup --client-variant=none --run-server=false
```

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

In the end, you should end up with an Oak server running, and with log output
something like:

```log
[2023-01-17T07:52:51Z INFO  oak_functions_launcher] read Wasm file from disk bin/weather_lookup.wasm (2045311 bytes)
[2023-01-17T07:52:51Z INFO  oak_functions_launcher] obtained public key (0 bytes)
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
[07:55:54 ✓:0,✗:0,⠇:1] ┌[oak-functions examples]
[07:55:54 ✓:0,✗:0,⠇:1] │┌[weather_lookup]
[07:55:54 ✓:0,✗:0,⠇:1] ││┌[wasm:weather_lookup:oak_functions/examples/weather_lookup/module/Cargo.toml]
[07:55:54 ✓:0,✗:0,⠇:1] │││ cargo -Zunstable-options build --target=wasm32-unknown-unknown --target-dir=/workspace/target/wasm --manifest-path=oak_functions/examples/weather_lookup/module/Cargo.toml --out-dir=/workspace/bin --release
    Finished release [optimized] target(s) in 0.20s
[07:55:54 ✓:0,✗:0,⠇:1] ││└─▶OK 263ms
[07:55:54 ✓:0,✗:0,⠇:1] ││┌[run]
[07:55:54 ✓:0,✗:0,⠇:1] │││┌[run clients]
[07:55:54 ✓:0,✗:0,⠇:1] ││││┌[rust]
[07:55:54 ✓:0,✗:0,⠇:1] │││││┌[build]
[07:55:54 ✓:0,✗:0,⠇:1] ││││││ cargo build --release --target=x86_64-unknown-linux-gnu --manifest-path=oak_functions_client/Cargo.toml
   Compiling oak_remote_attestation_noninteractive v0.1.0 (/workspace/oak_remote_attestation_noninteractive)
   Compiling oak_functions_client v0.1.0 (/workspace/oak_functions_client)
    Finished release [optimized] target(s) in 8.01s
[07:56:02 ✓:0,✗:0,⠇:1] │││││└─▶OK 8s
[07:56:02 ✓:0,✗:0,⠇:1] │││││┌[run]
[07:56:02 ✓:0,✗:0,⠇:1] ││││││ cargo run --release --target=x86_64-unknown-linux-gnu --manifest-path=oak_functions_client/Cargo.toml -- --uri=http://localhost:8080 --request={"lat":0,"lng":0} --expected-response-pattern=\{"temperature_degrees_celsius":.*\}
   Compiling oak_remote_attestation_noninteractive v0.1.0 (/workspace/oak_remote_attestation_noninteractive)
   Compiling oak_functions_client v0.1.0 (/workspace/oak_functions_client)
    Finished release [optimized] target(s) in 8.08s
     Running `target/x86_64-unknown-linux-gnu/release/oak_functions_client '--uri=http://localhost:8080' '--request={"lat":0,"lng":0}' '--expected-response-pattern=\{"temperature_degrees_celsius":.*\}'`
req: Request { body: [123, 34, 108, 97, 116, 34, 58, 48, 44, 34, 108, 110, 103, 34, 58, 48, 125] }
Response: [123, 34, 116, 101, 109, 112, 101, 114, 97, 116, 117, 114, 101, 95, 100, 101, 103, 114, 101, 101, 115, 95, 99, 101, 108, 115, 105, 117, 115, 34, 58, 50, 57, 125]
Response: "{\"temperature_degrees_celsius\":29}"
[07:56:11 ✓:0,✗:0,⠇:1] │││││└─▶OK 8s
[07:56:11 ✓:0,✗:0,⠇:1] ││││└[rust]─▶[OK] 16s
[07:56:11 ✓:0,✗:0,⠇:1] │││└[run clients]─▶[OK] 16s
[07:56:11 ✓:0,✗:0,⠇:1] ││└[run]─▶[OK] 16s
[07:56:11 ✓:0,✗:0,⠇:1] │└[weather_lookup]─▶[OK] 17s
[07:56:11 ✓:1,✗:0,⠇:0] └[oak-functions examples]─▶[OK] 17s
```

## Extracing vmlinux from your Linux installation

On Linux installations, you can extract the uncompressed Linux kernel ELF binary
from the compressed kernel at `/boot/vmlinuz-$(uname -r)`. You will need the
[extract-vmlinux](https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/plain/scripts/extract-vmlinux)
script from the kernel source code.

Assuming you have extract-vmlinux on your path, you can get vmlinux as follows:

```bash
extract-vmlinux /boot/vmlinuz-$(uname -r) > vmlinux
```

## Fuzz testing

We currently have fuzz testing enabled for Oak Functions on
[OSS-Fuzz](https://github.com/google/oss-fuzz/tree/master/projects/oak). In
addition, `xtask` has a command for running fuzz targets `run-cargo-fuzz`. This
command runs `cargo-fuzz` with the `-O` option for optimization, and supports
all `libFuzzer` options. These options must be provided as the last argument.
For instance, the following command runs all fuzz targets with a 2 seconds
timeout for each target.

```bash
xtask run-cargo-fuzz -- -max_total_time=2
```

The following lists all the `libFuzzer` options:

```bash
xtask --logs run-cargo-fuzz -- -help=1
```

Moreover, `target-name` could be specified to run a specific target.

```bash
xtask --logs run-cargo-fuzz --target-name=apply_policy -- -max_total_time=20
```

## Build and Release

We aspire for a transparent process for building and releasing Oak binaries. See
the [build and release documentation](release.md) for more information.
