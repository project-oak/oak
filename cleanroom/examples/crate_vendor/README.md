# crate_vendor

**A standalone replacement for [`cargo vendor`][cv].**

Parses a `Cargo.lock` file, downloads all registry crate archives from
[crates.io](https://crates.io), verifies SHA-256 checksums, and extracts them
into a local `vendor/` directory. Generates a `.cargo/config.toml` so that
`cargo build --frozen` uses only the vendored sources — no network required.

## Motivation

This tool is the first step toward an **allowlisted, cross-platform fetch
module**. The eventual architecture:

```text
┌─────────────────────────────┐      ┌────────────────────────────┐
│  crate_vendor (Wasm)        │      │  Sandboxed build (Docker)  │
│  ✅ Controlled network      │ ───→ │  ❌ No network             │
│  ✅ Auditable artifact      │ deps │  ✅ cargo build --frozen   │
│  ✅ Cross-platform          │      │  Consumes vendor/ only     │
└─────────────────────────────┘      └────────────────────────────┘
```

This tool compiles as a `wasm32-wasip2` component and runs inside the
[cleanroom][] sandbox. All I/O flows through the cleanroom SDK:

- **Filesystem** — `cleanroom_sdk::{read_file, write_file}` (proxied to the
  caller's sandbox via a Unix socket)
- **Output** — `cleanroom_sdk::{write_stdout_str, write_stderr_str}` with
  per-operation declassification
- **HTTP** — `cleanroom_sdk::http_get` with per-operation declassification
  (IFC-gated outgoing requests via the host)
- **CLI args** — parsed with `clap` via WASI `args`, forwarded by the cleanroom
  runtime

## Usage

Build the wasm component

```bash
bazel build //cleanroom/examples/crate_vendor:crate_vendor
```

### Via `cleanroom run` (server mode)

Start a cleanroom shell, then invoke the module with CLI args after `--`:

```bash
bazel run cleanroom -- shell
cleanroom run crate_vendor \
  --secrecy=caller --integrity=caller \
  -- --lockfile=cleanroom/examples/crate_vendor/testdata/Cargo.lock --output-dir=bin/vendor
```

The filesystem proxy runs inside the caller's sandbox, so `--lockfile` and
`--output-dir` are paths relative to the caller's working directory.

### Via `cleanroom run-local` (no server, local development)

```bash
cleanroom run-local \
  "$(bazel cquery --output=files //cleanroom/examples/crate_vendor:crate_vendor)" \
  -- --lockfile=cleanroom/examples/crate_vendor/testdata/Cargo.lock \
     --output-dir=/tmp/vendor
```

### Dry run — list crates without downloading

```bash
cleanroom run-local \
  "$(bazel cquery --output=files //cleanroom/examples/crate_vendor:crate_vendor)" \
  -- --lockfile=cleanroom/examples/crate_vendor/testdata/Cargo.lock --dry-run
```

```text
aho-corasick-1.1.3: https://static.crates.io/crates/aho-corasick/aho-corasick-1.1.3.crate
anyhow-1.0.98: https://static.crates.io/crates/anyhow/anyhow-1.0.98.crate
...
21 crates would be downloaded (dry run)
```

### Generate `.cargo/config.toml`

Pass `--config-dir` to automatically generate the Cargo config for offline
builds:

```bash
cleanroom run crate_vendor \
  --secrecy=caller --integrity=caller \
  -- --lockfile=Cargo.lock --output-dir=vendor --config-dir=.cargo
```

This writes `.cargo/config.toml` with:

```toml
[source.crates-io]
replace-with = "vendored-sources"

[source.vendored-sources]
directory = "vendor"
```

## CLI flags

| Flag           | Default      | Description                          |
| -------------- | ------------ | ------------------------------------ |
| `--lockfile`   | `Cargo.lock` | Path to the `Cargo.lock` file        |
| `--output-dir` | `vendor`     | Directory to extract crates into     |
| `--config-dir` |              | Write `.cargo/config.toml` here      |
| `--dry-run`    | `false`      | Print crate list without downloading |

## What it does

1. Parses `Cargo.lock` for `[[package]]` entries with
   `source = "registry+https://github.com/rust-lang/crates.io-index"`
2. Downloads each `.crate` archive from
   `https://static.crates.io/crates/{name}/{name}-{version}.crate` (see
   [registry web API][crate-dl])
3. Verifies the SHA-256 checksum against the `checksum` field in `Cargo.lock`
4. Extracts each archive into `vendor/{name}-{version}/`
5. Writes `.cargo-checksum.json` in each vendored crate directory
6. Optionally generates `.cargo/config.toml` pointing to the vendor directory

## Testing

```bash
bazel test //cleanroom/examples/crate_vendor:crate_vendor_integration_test
```

The test uses a checked-in `Cargo.lock` in `testdata/` (copied from
`oak_time/Cargo.lock`) so it is fully self-contained. It requires network access
to download crates from crates.io.

## Scope

- ✅ crates.io registry packages
- ❌ Git dependencies
- ❌ Path dependencies
- ❌ Alternate registries
- ❌ Version resolution (`cargo update`)

[cv]: https://doc.rust-lang.org/cargo/commands/cargo-vendor.html
[cleanroom]: /cleanroom/README.md
[crate-dl]:
  https://doc.rust-lang.org/cargo/reference/registry-web-api.html#download
