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
[19:27:50 ✓:0,✗:0,⠇:1] ┌[oak-functions examples]
[19:27:50 ✓:0,✗:0,⠇:1] │┌[weather_lookup]
[19:27:50 ✓:0,✗:0,⠇:1] ││┌[wasm:weather_lookup:oak_functions/examples/weather_lookup/module/Cargo.toml]
[19:27:50 ✓:0,✗:0,⠇:1] │││ cargo -Zunstable-options build --target=wasm32-unknown-unknown --target-dir=/workspace/target/wasm --manifest-path=oak_functions/examples/weather_lookup/module/Cargo.toml --out-dir=/workspace/bin --release
    Finished release [optimized] target(s) in 0.44s
[19:27:50 ✓:0,✗:0,⠇:1] ││└─▶OK 616ms
[19:27:50 ✓:0,✗:0,⠇:1] ││┌[wizer:bin/weather_lookup.wasm:bin/weather_lookup_init.wasm]
[19:27:50 ✓:0,✗:0,⠇:1] │││ wizer bin/weather_lookup.wasm -o=bin/weather_lookup_init.wasm
[19:27:50 ✓:0,✗:0,⠇:1] ││└─▶OK 71ms
[19:27:50 ✓:0,✗:0,⠇:1] ││┌[run]
[19:27:50 ✓:0,✗:0,⠇:1] │││┌[run clients]
[19:27:50 ✓:0,✗:0,⠇:1] ││││┌[rust]
[19:27:50 ✓:0,✗:0,⠇:1] │││││┌[build]
[19:27:50 ✓:0,✗:0,⠇:1] ││││││ cargo build --release --target=x86_64-unknown-linux-gnu --manifest-path=oak_functions/client/rust/Cargo.toml
    Finished release [optimized] target(s) in 0.49s
[19:27:51 ✓:0,✗:0,⠇:1] │││││└─▶OK 665ms
[19:27:51 ✓:0,✗:0,⠇:1] │││││┌[run]
[19:27:51 ✓:0,✗:0,⠇:1] ││││││ cargo run --release --target=x86_64-unknown-linux-gnu --manifest-path=oak_functions/client/rust/Cargo.toml -- --uri=http://localhost:8080 --request={"lat":0,"lng":0} --expected-response-pattern=\{"temperature_degrees_celsius":.*\}
    Finished release [optimized] target(s) in 0.51s
     Running `target/x86_64-unknown-linux-gnu/release/oak_functions_client '--uri=http://localhost:8080' '--request={"lat":0,"lng":0}' '--expected-response-pattern=\{"temperature_degrees_celsius":.*\}'`
req: Request { body: [123, 34, 108, 97, 116, 34, 58, 48, 44, 34, 108, 110, 103, 34, 58, 48, 125] }
Response: Response { status: Success, body: [...], length: 34 }
Response: "{\"temperature_degrees_celsius\":29}"
[19:27:53 ✓:0,✗:0,⠇:1] │││││└─▶OK 2s
[19:27:53 ✓:0,✗:0,⠇:1] ││││└[rust]─▶[OK] 2s
[19:27:53 ✓:0,✗:0,⠇:1] │││└[run clients]─▶[OK] 2s
[19:27:53 ✓:0,✗:0,⠇:1] ││└[run]─▶[OK] 2s
[19:27:53 ✓:0,✗:0,⠇:1] │└[weather_lookup]─▶[OK] 3s
[19:27:53 ✓:1,✗:0,⠇:0] └[oak-functions examples]─▶[OK] 3s
```

## Fuzz testing

We currently have fuzz testing enabled for Oak Functions on
[OSS-Fuzz](https://github.com/google/oss-fuzz/tree/master/projects/oak). In
addition, `xtask` has a command for running fuzz targets `run-fuzz-targets`.
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
xtask --logs run-cargo-fuzz --crate-name=loader --target-name=wasm_invoke -- -max_total_time=20
```

## Retrieving a previously-built binary and its provenance

Every time a pull-request is merged to `main` the
`oak_functions_freestanding_bin` binary is built and uploaded to `ent`.
Similarly, a
[signed SLSA3+ provenance is generated](https://github.com/slsa-framework/slsa-github-generator/blob/04f1fe0c7b7902c9a95f4c7eef2dc04cf0f8e6a7/internal/builders/generic/README.md)
for it and uploaded to GitHub. The signed provenance is also uploaded to the
public instance of Rekor hosted by Sigstore at https://rekor.sigstore.dev, and
can be downloaded from it.

This section describes how the binary and its provenance can be downloaded.

Once a pull-request is merged to `main` and all CI steps are executed on branch
`main`, an automated comment is added to the pull-request containing the hash of
the `oak_functions_freestanding_bin` binary:

```bash
d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc  ./oak_functions_freestanding_bin/target/x86_64-unknown-none/release/oak_functions_freestanding_bin
```

### Step 1: Download the binary

The hash of the binary
(`d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc`) can be used
to download the binary from `ent`, with the following command using the
[ent HTTP API](https://github.com/google/ent#raw-http-api):

```bash
$ curl --output oak_functions_from_ent  https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 2327k    0 2327k    0     0  3637k      0 --:--:-- --:--:-- --:--:-- 3636k
```

### Step 2: Download the provenance

The provenance can be downloaded from Rekor or the GitHub actions workflow that
generated the binary and its provenance (i.e.,
[Build Provenance](https://github.com/project-oak/oak/actions/workflows/provenance.yaml))

#### Download from Rekor

To fetch the provenance from Rekor, one has to first find the Rekor LogEntries
that refer to the binary (via its SHA256 hash), using the `search` command
provided by `rekor-cli`
([installation instructions](https://docs.sigstore.dev/rekor/installation/)):

```bash
$ rekor-cli search --sha d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc
Found matching entries (listed by UUID):
24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
```

Usually there is only one entry, but it is possible to get multiple entires.
Alternatively, one can use the SHA1 Git commit hash to find the provenances
corresponding to that commit hash:

```bash
$ rekor-cli search --sha 1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6
Found matching entries (listed by UUID):
24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
```

Note that `rekor-cli` by default uses https://rekor.sigstore.dev as the Rekor
server.

Using the UUID
(24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576),
one can retrieve the provenance:

```bash
$ rekor-cli get --uuid 24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
LogID: c0d23d6ad406973f9559f3ba2d1ca01f84147d8ffc5b8445c224f98b9591801d
Attestation: {"_type":"https://in-toto.io/Statement/v0.1","predicateType":"https://slsa.dev/provenance/v0.2","subject":[{"name":"oak_functions_freestanding_bin","digest":{"sha256":"d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc"}}],"predicate":{"builder":{"id":"https://github.com/slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@refs/tags/v1.2.0"},"buildType":"https://github.com/slsa-framework/slsa-github-generator@v1","invocation":{"configSource":{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6"},"entryPoint":".github/workflows/provenance.yaml"},"parameters":{},"environment":{ "/* GitHub context */"}},"metadata":{"buildInvocationID":"3230206088-1","completeness":{"parameters":true,"environment":false,"materials":false},"reproducible":false},"materials":[{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6"}}]}}
Index: 4920248
IntegratedTime: 2022-10-11T21:18:18Z
UUID: 24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
Body: {
  "IntotoObj": {
    "content": {
      "hash": {
        "algorithm": "sha256",
        "value": "2268194f93bf9db7de6344a665ae38de791e7adc30ecc315000b77b24d0a4a60"
      },
      "payloadHash": {
        "algorithm": "sha256",
        "value": "9db814f8b10fc3d9442eb322c265fb47105a85fc35fa62a660a83f5bb0f66622"
      }
    },
    "publicKey": "LS0tLS1CRUdJTiBDRVJUSUZJQ0FURS0tLS0tCk1JSUR2RENDQTBLZ0F3SUJBZ0lVQnQzRkpSUG9LQVpicU43M2VOaDk4QndRdWRZd0NnWUlLb1pJemowRUF3TXcKTnpFVk1CTUdBMVVFQ2hNTWMybG5jM1J2Y21VdVpHVjJNUjR3SEFZRFZRUURFeFZ6YVdkemRHOXlaUzFwYm5SbApjbTFsWkdsaGRHVXdIaGNOTWpJeE1ERXhNakV4T0RFNFdoY05Nakl4TURFeE1qRXlPREU0V2pBQU1Ga3dFd1lICktvWkl6ajBDQVFZSUtvWkl6ajBEQVFjRFFnQUV5NnNNY3FRcVhXcXJhclJONi95SmRlRnQ2L1VWUVI0QWh2ay8KRzBMT1BqRVd6ZHNSZFdvcUJiYWtUM05PWEdGOThjSWN3M29BS1ZSbUhKZkwvTGJPMDZPQ0FtRXdnZ0pkTUE0RwpBMVVkRHdFQi93UUVBd0lIZ0RBVEJnTlZIU1VFRERBS0JnZ3JCZ0VGQlFjREF6QWRCZ05WSFE0RUZnUVVtQlZ1CkhyTmtHVjVheUxHR2ErWkJ2V1Vvb29Zd0h3WURWUjBqQkJnd0ZvQVUzOVBwejFZa0VaYjVxTmpwS0ZXaXhpNFkKWkQ4d2dZUUdBMVVkRVFFQi93UjZNSGlHZG1oMGRIQnpPaTh2WjJsMGFIVmlMbU52YlM5emJITmhMV1p5WVcxbApkMjl5YXk5emJITmhMV2RwZEdoMVlpMW5aVzVsY21GMGIzSXZMbWRwZEdoMVlpOTNiM0pyWm14dmQzTXZaMlZ1ClpYSmhkRzl5WDJkbGJtVnlhV05mYzJ4ellUTXVlVzFzUUhKbFpuTXZkR0ZuY3k5Mk1TNHlMakF3T1FZS0t3WUIKQkFHRHZ6QUJBUVFyYUhSMGNITTZMeTkwYjJ0bGJpNWhZM1JwYjI1ekxtZHBkR2gxWW5WelpYSmpiMjUwWlc1MApMbU52YlRBU0Jnb3JCZ0VFQVlPL01BRUNCQVJ3ZFhOb01EWUdDaXNHQVFRQmc3OHdBUU1FS0RGaU1USTRabUl5Ck5UVTJaVFJpWkdOak5HWTVNalUxTWpZMU5HSm1ZbU5oT1dReVptSTRZell3SGdZS0t3WUJCQUdEdnpBQkJBUVEKUW5WcGJHUWdVSEp2ZG1WdVlXNWpaVEFkQmdvckJnRUVBWU8vTUFFRkJBOXdjbTlxWldOMExXOWhheTl2WVdzdwpIUVlLS3dZQkJBR0R2ekFCQmdRUGNtVm1jeTlvWldGa2N5OXRZV2x1TUlHSkJnb3JCZ0VFQWRaNUFnUUNCSHNFCmVRQjNBSFVBQ0dDUzhDaFMvMmhGMGRGcko0U2NSV2NZckJZOXd6alNiZWE4SWdZMmIzSUFBQUdEeU9taUpnQUEKQkFNQVJqQkVBaUI3T3VDOGtMSkFiMk9qK2ozL2ZQRFlqeFE1V1Z0cFNRM0VHU2hjQzJWQUFBSWdHVWd6VVdydQpPV2dRYmhaa2VrZm9GMzFHenQvRXh5NEhVVXJWZkJyMUdmc3dDZ1lJS29aSXpqMEVBd01EYUFBd1pRSXhBUDlpCk5yNHFFYU1pdlMySGErN2JIaTh1MncvbTZWczd1S21sN1FhRlFFaUN4K0l5TlZMNkh3c1BZTkxnNVEwT3JRSXcKZGMyRlozT0FPUXZxaXJ4MlhGbDBPMytpczFWYjB5Wi9ic09ud2IweTV2Y0h6SVoyT1B0ejV6eDcyZFY4L295SQotLS0tLUVORCBDRVJUSUZJQ0FURS0tLS0tCg=="
  }
}
```

In addition to the provenance (in `Attestation`), the response contains
additional fields, including the `Body.IntotoObj` object. The `payloadHash` in
this object is the SHA256 hash of the provenance.

Alternatively, the provenance can be retrieved, as part of a Rekor LogEntry,
using the Rekor HTTP API:

```bash
$ curl --output signed-provenance-entry https://rekor.sigstore.dev/api/v1/log/entries/24296fb24b8ad77a872690e11780e927d9eddd1bc3a598e5490ad1c75fe039289a5dccc5b4d71576
  % Total    % Received % Xferd  Average Speed   Time    Time     Time  Current
                                 Dload  Upload   Total   Spent    Left  Speed
100 17907    0 17907    0     0  21765      0 --:--:-- --:--:-- --:--:-- 21758
```

The downloaded file is a JSON document. The provenance is included in the
`attestation.data` field as a base64-encoded string, and can be extracted using
the following command:

```bash
$ jq .[].attestation.data signed-provenance-entry | tr --delete '"' | base64 --decode
{"_type":"https://in-toto.io/Statement/v0.1","predicateType":"https://slsa.dev/provenance/v0.2","subject":[{"name":"oak_functions_freestanding_bin","digest":{"sha256":"d059c38cea82047ad316a1c6c6fbd13ecf7a0abdcc375463920bd25bf5c142cc"}}],"predicate":{"builder":{"id":"https://github.com/slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@refs/tags/v1.2.0"},"buildType":"https://github.com/slsa-framework/slsa-github-generator@v1","invocation":{"configSource":{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6"},"entryPoint":".github/workflows/provenance.yaml"},"parameters":{},"environment":{ "/* GitHub context */"}},"metadata":{"buildInvocationID":"3230206088-1","completeness":{"parameters":true,"environment":false,"materials":false},"reproducible":false},"materials":[{"uri":"git+https://github.com/project-oak/oak@refs/heads/main","digest":{"sha1":"1b128fb2556e4bdcc4f92552654bfbca9d2fb8c6"}}]}}
```

#### Downloading provenance from GitHub

The provenance and the signature over it can be downloaded directly from GitHub.
For `oak_functions_freestanding_bin` it is stored under the name
`oak_functions_freestanding_bin.intoto.jsonl`, as an attachment on the GitHub
actions workflow. This file is in
[DSSE format](https://github.com/secure-systems-lab/dsse/blob/master/protocol.md):

```json
{
  "payloadType": "application/vnd.in-toto+json",
  "payload": "<base64-encoded provenance>",
  "signatures": [
    {
      "keyid": "",
      "sig": "MEUCIQCBAUFYTJV6K6/nvCszhYwScOrkHHSaLrqQYzuWM5BGBwIgbmwnn7iVxEM2nEK87mSLxovXuSnKqtZ9Vdk7fn5IGrY=",
      "cert": "-----BEGIN CERTIFICATE-----\nMIIDvTCCA0OgAwIBAgIUbYxISaXl3PtnznMvAqVxAEwwEyMwCgYIKoZIzj0EAwMw\nNzEVMBMGA1UEChMMc2lnc3RvcmUuZGV2MR4wHAYDVQQDExVzaWdzdG9yZS1pbnRl\ncm1lZGlhdGUwHhcNMjIxMDEyMTM0NjU5WhcNMjIxMDEyMTM1NjU5WjAAMFkwEwYH\nKoZIzj0CAQYIKoZIzj0DAQcDQgAEFk0sopU9+056g0+AwC0ZSfLLkezYQdJo066J\n4zwISwhTzWhLWCTBIop+IklTOl7rA4EL607Q8KYcUJ9JYyrAJ6OCAmIwggJeMA4G\nA1UdDwEB/wQEAwIHgDATBgNVHSUEDDAKBggrBgEFBQcDAzAdBgNVHQ4EFgQUfnSL\nzXKuuwyGguvltiSECavHt0wwHwYDVR0jBBgwFoAU39Ppz1YkEZb5qNjpKFWixi4Y\nZD8wgYQGA1UdEQEB/wR6MHiGdmh0dHBzOi8vZ2l0aHViLmNvbS9zbHNhLWZyYW1l\nd29yay9zbHNhLWdpdGh1Yi1nZW5lcmF0b3IvLmdpdGh1Yi93b3JrZmxvd3MvZ2Vu\nZXJhdG9yX2dlbmVyaWNfc2xzYTMueW1sQHJlZnMvdGFncy92MS4yLjAwOQYKKwYB\nBAGDvzABAQQraHR0cHM6Ly90b2tlbi5hY3Rpb25zLmdpdGh1YnVzZXJjb250ZW50\nLmNvbTASBgorBgEEAYO/MAECBARwdXNoMDYGCisGAQQBg78wAQMEKGEzN2FmMGVl\nM2E4MDZhNDYyZThmN2Q1NzkyMTFhMTNiZTE3OGIyOGQwHgYKKwYBBAGDvzABBAQQ\nQnVpbGQgUHJvdmVuYW5jZTAdBgorBgEEAYO/MAEFBA9wcm9qZWN0LW9hay9vYWsw\nHQYKKwYBBAGDvzABBgQPcmVmcy9oZWFkcy9tYWluMIGKBgorBgEEAdZ5AgQCBHwE\negB4AHYACGCS8ChS/2hF0dFrJ4ScRWcYrBY9wzjSbea8IgY2b3IAAAGDzHLNvwAA\nBAMARzBFAiAuNExKS7cP5J8N2sP318EXCUTz/zq0zoXZHqDaSvIM1AIhALzcaTG8\npIXPRBfPRr0J5J7EO+HTCgaAZsXbiUjOOs5iMAoGCCqGSM49BAMDA2gAMGUCMQD6\nqMASnc6IeBiiGbAFjdchyhCxCHunb+ZeLdlIu95QKKKOSGy/eTuu5B06V/1gk1sC\nMHCw+W4BrkqRIw4CvCpjdtVyv1KUplmysXHs2jQ+ATokAccs4o4DRHUn5AFq2FR6\nbA==\n-----END CERTIFICATE-----\n"
    }
  ]
}
```

TODO: Describe the relation between the cert in DSSE format, and the public key
in the response from `rekor-cli`.
