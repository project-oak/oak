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
./scripts/docker_run cargo nextest run --package=oak_functions_launcher
```

This will run integration tests for Oak Functions, which involve building the
Oak Functions Enclave Application, its untrusted launcher, various Oak Functions
Wasm modules and a client for the Application, then run them all, with log
output ending something like the following:

```log
        PASS [   0.007s] oak_functions_launcher lookup::test_chunk_up_lookup_data_empty
        PASS [   0.007s] oak_functions_launcher lookup::test_chunk_up_lookup_data_exceed_bound
        PASS [   0.007s] oak_functions_launcher lookup::test_chunk_up_lookup_data_in_bound
        PASS [   1.472s] oak_functions_launcher::integration_test test_launcher_looks_up_key
        PASS [   1.472s] oak_functions_launcher::integration_test test_load_large_lookup_data
        PASS [  49.419s] oak_functions_launcher::integration_test test_launcher_echo_virtual
        PASS [  49.425s] oak_functions_launcher::integration_test test_launcher_key_value_lookup_virtual
        SLOW [> 60.000s] oak_functions_launcher::integration_test test_launcher_weather_lookup_virtual
        PASS [ 115.656s] oak_functions_launcher::integration_test test_launcher_weather_lookup_virtual
------------
     Summary [ 109.045s] 8 tests run: 8 passed (3 slow, 3 leaky), 1 skipped
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

Using [`flake.nix`](/flake.nix) from within the Oak repo to get a Nix
development subshell in which a completely deterministic environment (e.g.
compilers, dev tools) is available:

```console
nix develop
```

Note that this may take a while (up to 10 minutes) on the first run, since Nix
has to download all the dependencies from scratch. It will be almost instant in
future invocations, unless [`flake.nix`](/flake.nix) changes.

This will finish with

```
I have no name!@<your-user-name>:~/oak$
```

Some things to try:

- See where tools are installed from within the dev shell (this output might be
  out of date when [`flake.nix`](/flake.nix) changes):

  ```console
  $ which rustc
  /nix/store/mrf09022h38ykgsfb50xcv3q1izf5gac-rust-default-1.69.0-nightly-2023-02-15/bin/rustc
  ```

- Add a new dependency to the list, and see it reflected in the dev shell:

  - (if you are not already in the dev shell) enter the default dev shell:

    ```console
    nix develop
    ```

  - check `ponysay` is not installed on the host or the default dev shell:

    ```console
    $ ponysay hello
    bash: command not found: ponysay
    ```

  - add `ponysay` to the list of `packages` in [`flake.nix`](/flake.nix), e.g.
    just below `protobuf`
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

## Run Oak Functions Examples

Running the integration tests for Oak Functions will confirm that all core
prerequisites have been installed.

Run them inside Docker with:

```bash
cargo nextest run --package=oak_functions_launcher
```

Each test:

- builds the Oak Stage0 firmware
- builds the Oak Restricted Kernel binary
- builds the Oak Functions Enclave Application
- builds the Oak Functions Launcher
- builds a particular Oak Functions Application, i.e. Rust code that is compiled
  to a WebAssembly module binary
- starts the Oak Functions Launcher as a background process, passing it the
  compiled WebAssembly for the Oak Functins Application (which it then runs in a
  WebAssembly engine)
- invokes the Rust gRPC client for the Application
- closes everything down.

## Extracting vmlinux from your Linux installation

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
