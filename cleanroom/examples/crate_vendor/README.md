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

This tool compiles as a `wasm32-wasip2` component and runs inside [wasmtime][].
The host provides HTTP via [`wasi:http`][wasi-http] — making the fetch module
the _only_ component with network access.

## Usage

Build the wasm component

```bash
bazel build //cleanroom/examples/crate_vendor:crate_vendor
```

Run with wasmtime (requires wasi:http access)

```console
$ wasmtime run --wasi=http --wasi=cli --dir=. \
  "$(bazel cquery --output=files //cleanroom/examples/crate_vendor:crate_vendor)" \
  --lockfile=cleanroom/examples/crate_vendor/testdata/Cargo.lock --output-dir=$(mktemp --directory)
vendored 21 crates (21 downloaded, 0 already present) into "/tmp/tmp.wNCCR9OAzN"
```

Dry run — just print what would be downloaded

```console
$ wasmtime run --wasi=http --wasi=cli --dir=. \
  "$(bazel cquery --output=files //cleanroom/examples/crate_vendor:crate_vendor)" \
  --lockfile=cleanroom/examples/crate_vendor/testdata/Cargo.lock --dry-run
aho-corasick-1.1.3: https://static.crates.io/crates/aho-corasick/aho-corasick-1.1.3.crate
anyhow-1.0.98: https://static.crates.io/crates/anyhow/anyhow-1.0.98.crate
autocfg-1.5.0: https://static.crates.io/crates/autocfg/autocfg-1.5.0.crate
bytes-1.10.1: https://static.crates.io/crates/bytes/bytes-1.10.1.crate
either-1.15.0: https://static.crates.io/crates/either/either-1.15.0.crate
googletest-0.14.2: https://static.crates.io/crates/googletest/googletest-0.14.2.crate
googletest_macro-0.14.2: https://static.crates.io/crates/googletest_macro/googletest_macro-0.14.2.crate
itertools-0.14.0: https://static.crates.io/crates/itertools/itertools-0.14.0.crate
memchr-2.7.5: https://static.crates.io/crates/memchr/memchr-2.7.5.crate
num-traits-0.2.19: https://static.crates.io/crates/num-traits/num-traits-0.2.19.crate
proc-macro2-1.0.95: https://static.crates.io/crates/proc-macro2/proc-macro2-1.0.95.crate
prost-0.14.1: https://static.crates.io/crates/prost/prost-0.14.1.crate
prost-derive-0.14.1: https://static.crates.io/crates/prost-derive/prost-derive-0.14.1.crate
prost-types-0.14.1: https://static.crates.io/crates/prost-types/prost-types-0.14.1.crate
quote-1.0.40: https://static.crates.io/crates/quote/quote-1.0.40.crate
regex-1.11.1: https://static.crates.io/crates/regex/regex-1.11.1.crate
regex-automata-0.4.9: https://static.crates.io/crates/regex-automata/regex-automata-0.4.9.crate
regex-syntax-0.8.5: https://static.crates.io/crates/regex-syntax/regex-syntax-0.8.5.crate
rustversion-1.0.21: https://static.crates.io/crates/rustversion/rustversion-1.0.21.crate
syn-2.0.104: https://static.crates.io/crates/syn/syn-2.0.104.crate
unicode-ident-1.0.18: https://static.crates.io/crates/unicode-ident/unicode-ident-1.0.18.crate

21 crates would be downloaded (dry run)
```

[wasmtime]: https://wasmtime.dev/
[wasi-http]: https://github.com/WebAssembly/wasi-http

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
[crate-dl]:
  https://doc.rust-lang.org/cargo/reference/registry-web-api.html#download
