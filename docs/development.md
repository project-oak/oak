# Oak Development

Development of Oak is mainly supported within a [Nix](https://nixos.org/)
environment on Linux, which guarantees that all the developers are using the
same exact version of all the compilers and build tools, and that this is also
in sync with what is used by the Continuous Integration (CI) system.

This is also necessary (though not by itself sufficient) to enable building Oak
binaries in a detereministic and reproducible way, which in turn allows Oak to
be
[transparently released](https://github.com/project-oak/oak/tree/main/docs/tr/README.md).

Mac and Windows development is not officially supported.

## Install Nix

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

## Nix Development Shell

The [`flake.nix`](/flake.nix) file within this repository defines a Nix
development shell in which a completely deterministic environment (e.g.
compilers, dev tools) is available.

In order to instantiate a Nix shell, see one of the following options.

### With `direnv`

[`direnv`](https://direnv.net) is a shell utility that automatically loads a
development environment (in this case Nix) when `cd`ing into a specific folder.

To install `direnv`, follow the
[official instructions](https://direnv.net/#basic-installation). Make sure to
install the appropriate [shell hook](https://direnv.net/docs/hook.html) too.

Once installed, `cd` to this repository root, and run `direnv allow` in the
terminal; this only needs to be done the first time, or when the
[`.envrc`](/.envrc) file changes.

From then on, every time you `cd` in that same folder (or any subfolder), the
appropriate Nix configuration will be automatically loaded in your existing
shell, and unloaded again when you `cd` out of the folder.

Note that it may take some time (up to 10 minutes) for `direnv` to apply the Nix
shell configuration, especially the first time or whenever a large number of
dependencies changed since the previous execution.

It is also recommended to install the
[`direnv`](https://marketplace.visualstudio.com/items?itemName=mkhl.direnv)
extension for VS Code.

#### Remote development

[Quick (90s) setup video walkthrough (internal only)](https://screencast.googleplex.com/cast/NTU0NjA4OTg1Njg5MjkyOHxmZDRlYzhhMS1hYQ)

To develop on a remote machine, use the native
[Remote SSH extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-ssh).

Nix must be installed on the remote machine; follow the same
[installation instructions](#install-nix) above.

Make sure the `direnv` VS Code extension is also installed on the remote host,
so that the correct binaries are picked up by VS Code from the Nix shell
remotely.

After connecting for the first time, make sure the following settings are set
remotely:

```json
{
  "rust-analyzer.server.path": "rust-analyzer"
}
```

This, together with the `direnv` extension, allows the `rust-analyzer` extension
to invoke the `rust-analyzer` binary from the Nix shell remotely, instead of
expecting to install it separately.

It may be necessary to restart the remote extension host the first time after
this setup.

### Without `direnv`

To get a Nix development shell:

```console
nix develop
```

Note that this may take a while (up to 10 minutes) on the first run, since Nix
has to download all the dependencies from scratch. It will be almost instant in
future invocations, unless [`flake.nix`](/flake.nix) changes.

This will finish with

```console
I have no name!@<your-user-name>:~/oak$
```

### Things to try

Some things to try once you are in a nix shell (in whichever way described
above):

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
  - re-create a new dev shell (only needed if not using `direnv`):

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

### Caching

The setup optionally uses cachix for caching nix derivations.

The `cachix` CLI is already installed in the nix setup locally. In order to be
able to **write** to the remote cache, first authorize with the following
command, using the token shared in
[valentine](https://valentine.corp.google.com/#/show/1721691800385167):

```bash
cachix authtoken <TOKEN>
```

Then, in order to populate cache for a local derivation, first build it locally,
and then push it to the remote cache. The command below is running the `true`
command inside the default nix shell, and creating a profile called
`dev-profile` that links to it; then the `cachix` CLI reads that symlink and
pushes all the artifacts to the cache, if they are not already there.

```bash
nix develop --profile dev-profile --command true
cachix push oak-1 dev-profile
```

To view stats about the cache, see https://app.cachix.org/cache/oak-1 .

## Run Oak Functions Examples

Running the integration tests for Oak Functions will confirm that all core
prerequisites have been installed.

Run them with:

```bash
bazel test //oak_functions_launcher:oak_functions_launcher_integration_test
```

Each test:

- builds the [Oak Stage0 firmware](/stage0_bin)
- builds the [Oak Restricted Kernel binary](/oak_restricted_kernel_bin)
- builds the
  [Oak Functions Enclave Application](/enclave_apps/oak_functions_enclave_app)
- builds the [Oak Functions Launcher](/oak_functions_launcher)
- builds a particular Oak Functions Application, i.e. Rust code that is compiled
  to a WebAssembly module binary
- starts the Oak Functions Launcher as a background process, passing it the
  compiled WebAssembly for the Oak Functions Application (which it then runs in
  a WebAssembly engine)
- invokes the Rust gRPC client for the Application
- closes everything down.

## Build and Release

We aspire for a transparent process for building and releasing Oak binaries. See
the [build and release documentation](release.md) for more information.

## Mac OS

Support for Mac OS is very limited at the moment.

The recommended way of installing Nix is via the
[determinate installer](https://docs.determinate.systems/).

Once that is installed, the instructions above should mostly work. Note that
several dependencies are excluded from tne nix shell for Mac OS, therefore not
everything will actually build. The linux-only dependencies are behind an
optional in the `flake.nix` file:

```nix
              ...
              # Linux-specific dependencies.
              lib.optionals stdenv.isLinux [
                systemd
              ];
              ...
```

To test whether things work end-to-end, you can try running the following
command:

```console
bazel run linter:linter
```

which should work natively.
