# Cleanroom

**A sandboxed WebAssembly runner with Information Flow Control (IFC) for humans
and LLM agents.**

Cleanroom executes Wasm modules in a secure environment with fine-grained
tracking of data confidentiality. Modules interact via standard WASI, while the
host silently tracks which secrets and files each module has accessed and
enforces declassification policies before allowing data to leave (e.g. via
HTTP).

## Quick start

The fastest way to try cleanroom — a single command builds everything, starts
the IFC server, and drops you into a sandboxed shell:

```bash
# 1. Generate the policy file (computes module digests, creates module store)
bazel run cleanroom/tools/generate_policy

# 2. Launch the sandboxed shell
bazel run cleanroom -- shell
```

That's it! The shell is now network-isolated with the sandbox policy printed on
entry. Inside the shell you can run modules:

```console
$ echo "hello world" | cleanroom run to_uppercase_wasm
HELLO WORLD

$ cleanroom run redact_secret_wasm
Redacted secret: top-**********

# Network is blocked.
$ curl wttr.in
curl: (7) Failed to connect to wttr.in port 80 after 4 ms: Could not connect to server

# File system outside of the current folder is not writeable.
$ touch /tmp/x
touch: cannot touch '/tmp/x': Operation not permitted
```

The `shell` subcommand handles everything automatically:

- Starts a `cleanroom server` daemon in the background
- Creates a temporary Unix socket for client ↔ server communication
- On macOS, uses `sandbox-exec` to block IP networking and restrict file writes
  to the current workspace directory
- Prints the applied sandbox profile so you can see exactly what's enforced
- Cleans up the server and socket when you type `exit`

## Architecture

Cleanroom operates in two modes:

### 1. Direct mode (`cleanroom run-local`)

The original mode. Runs a single Wasm module in a zero-import sandbox using the
Oak Functions ABI. No filesystem, network, or env vars. stdin → wasm → stdout
only.

```bash
echo "hello" | bazel run cleanroom -- run-local to_uppercase_wasm
```

### 2. Server/client mode (`cleanroom shell`)

The full IFC-enforcing mode. Launches a network-isolated shell connected to a
host-side daemon. On macOS this uses `sandbox-exec`; on Linux you can use Docker
or Podman.

```text
┌──────────────────────────────────────────────┐
│  Sandboxed shell (sandbox-exec / container)   │
│                                               │
│  Interactive shell (bash/zsh)                 │
│    IP networking blocked                      │
│    File writes restricted to workspace        │
│    Rest of filesystem read-only               │
│                                               │
│  cleanroom client run --module=crate_vendor   │
│    └── $CLEANROOM_SOCKET                      │
└──────────────────┬───────────────────────────-┘
                   │ Unix domain socket
                   ▼
┌──────────────────────────────────────────────┐
│  cleanroom server (host process)              │
│                                               │
│  wasmtime + WASI + IFC label tracking         │
│  Custom Filesystem ABI (IFC-gated proxy)     │
│  Data cells (labeled)                         │
│  Policy file (read-only)                      │
└──────────────────────────────────────────────┘
```

The container has **zero network access**. The only way out is through cleanroom
modules, each tracked by IFC and subject to declassification policy.

## Information Flow Control

### Why IFC?

An LLM agent working in a repo has access to source code, secrets (API keys in
env vars), and the network (via tools). Without IFC, a compromised or
misbehaving module could exfiltrate secrets by encoding them into HTTP requests.

IFC tracks **which sensitive data a module has seen** and blocks output to
channels that shouldn't receive that data.

### Labels

Each resource (env var, data cell) carries a **label** — a set of
confidentiality categories:

| Resource                  | Label               |
| ------------------------- | ------------------- |
| Files in `/workspace/`    | `{local_repo}`      |
| `GITHUB_API_TOKEN`        | `{github}`          |
| `GOOGLE_CALENDAR_API_KEY` | `{google_calendar}` |
| HTTP (public internet)    | `∅` (public)        |
| Agent stdin               | `{local_repo}`      |

### Computation label (`pc`)

The host tracks a `pc` (program counter label) per module invocation. When a
module reads a labeled resource, `pc` is joined (set union'd) with the
resource's label:

```text
pc = {local_repo}              ← stdin taint
  module reads GITHUB_API_TOKEN
pc = {local_repo, github}      ← accumulated taint
```

### Declassification

Before writing to an output channel (HTTP), `pc` must **flow to** the channel's
label. Since HTTP is public (`∅`), `pc` must be empty.

Declassification is **explicit** — the module must call
`ifc::declassify(categories)` to strip categories from `pc`. The host verifies
each category is in the module's `can_declassify` privilege (from the policy
file).

This design is deliberate:

- **Not automatic.** A module's privilege doesn't automatically apply. The
  module must consciously invoke `ifc::declassify` at a specific point in its
  code. This makes the security decision auditable in the module's source.
- **Two distinct types.** The codebase uses [`Label`](src/ifc.rs) (data taint)
  vs [`DeclassificationPrivilege`](src/ifc.rs) (policy authority) so they cannot
  be accidentally confused.

### What modules see

Modules use **standard WASI** for all I/O. The only IFC-specific APIs are two
optional host imports:

```text
ifc::get_label()       → current pc categories
ifc::declassify(cats)  → strip categories (privilege-checked)
```

Modules that don't call these are just normal WASI programs. The host still
tracks labels — the module just can't declassify, so any taint stays.

## Policy file

The policy is a TOML file that configures the IFC environment. It defines
environment variable labels and module privileges:

```toml
# crate_vendor — reads Cargo.lock, fetches crates via HTTP.
[[module]]
name           = "crate_vendor"
digest         = "sha256:aaa..."
can_declassify = ["local_repo"]
```

The policy file is part of the **Trusted Computing Base (TCB)**.

## Security model

| Property          | Direct mode | Server/client mode                   |
| ----------------- | ----------- | ------------------------------------ |
| Filesystem access | ❌ None     | ✅ Via custom FS ABI (IFC-gated)     |
| Network access    | ❌ None     | ✅ Via WASI HTTP (IFC-gated)         |
| Secrets           | ❌ None     | ✅ Labeled data cells / env vars     |
| IFC enforcement   | ❌ No       | ✅ Category-based labels             |
| Fuel / CPU budget | ✅ wasmtime | ✅ wasmtime                          |
| Memory budget     | ✅ wasmtime | ✅ wasmtime                          |
| Network isolation | N/A         | ✅ `sandbox-exec` / `--network=none` |

## Building

```bash
# Build the cleanroom binary
bazel build //cleanroom:cleanroom

# Build all example modules
bazel build //cleanroom/examples/...

# Run all tests (unit + integration)
bazel test //cleanroom:cleanroom_integration_test
```

## Advanced: manual server/client

If you want to run the server and client separately (e.g. for debugging or
custom setups):

```bash
# Terminal 1 — start the server
./bazel-bin/cleanroom/cleanroom server \
  --policy-file=cleanroom/example_policy.toml \
  --socket=/tmp/cleanroom.sock \
  --module-store=/tmp/modules

# Terminal 2 — run a module
export CLEANROOM_SOCKET=/tmp/cleanroom.sock
echo "hello world" | ./bazel-bin/cleanroom/cleanroom client run \
  --module=to_uppercase_wasm
```

## Examples

| Module          | Source                                               | Description                            |
| --------------- | ---------------------------------------------------- | -------------------------------------- |
| `to_uppercase`  | [`examples/to_uppercase/`](examples/to_uppercase/)   | ASCII uppercase                        |
| `reverse`       | [`examples/reverse/`](examples/reverse/)             | Reverse bytes                          |
| `word_count`    | [`examples/word_count/`](examples/word_count/)       | Count lines/words/bytes (like `wc`)    |
| `redact_secret` | [`examples/redact_secret/`](examples/redact_secret/) | Reads and redacts secrets (IFC demo)   |
| `weather`       | [`examples/weather/`](examples/weather/)             | Reads city from secrets, shows wttr.in |
| `crate_vendor`  | [`examples/crate_vendor/`](examples/crate_vendor/)   | Vendored crate downloads               |

## Writing your own module

### Pure sandbox module (Oak Functions ABI)

For modules that need no filesystem, network, or secrets:

```rust
#![no_std]
extern crate alloc;
use alloc::vec::Vec;

#[unsafe(no_mangle)]
pub extern "C" fn main() {
    cleanroom_sdk::run_with(|input: &[u8]| -> Vec<u8> {
        input.iter().map(|b| b.to_ascii_uppercase()).collect()
    });
}
```

### WASI module with IFC

For modules that access files, env vars, or HTTP:

```rust
fn main() {
    // Read Cargo.lock — host silently taints pc with {local_repo}.
    let lockfile = std::fs::read_to_string("/workspace/Cargo.lock").unwrap();

    // Parse and build download URLs...
    let urls = parse_cargo_lock(&lockfile);

    // Explicitly declassify before making HTTP calls.
    cleanroom_sdk::declassify(&["local_repo"]).unwrap();

    // Now HTTP is allowed.
    for url in urls {
        let bytes = http_get(&url);
        // ...
    }
}
```

## Project structure

```text
cleanroom/
  BUILD                   — Bazel: binary + integration tests
  README.md               — This file
  example_policy.toml     — Example policy (generated by tools/generate_policy)
  secrets/                — Example secrets directory (IFC-labeled)
  src/
    main.rs               — Entry point: run, server, client, shell subcommands
    ifc.rs                — IFC label types (Label, DeclassificationPrivilege,
                            ComputationLabel) and lattice operations
    policy.rs             — TOML policy parser
    protocol.rs           — RPC protocol (bincode over Unix socket)
    server.rs             — Host-side IFC server daemon
    client.rs             — Thin client for inside the container
    shell.rs              — Sandboxed shell launcher (sandbox-exec / Docker)
  sdk/
    lib.rs                — Guest SDK (Oak Functions ABI + IFC imports)
    BUILD
  examples/
    to_uppercase/         — ASCII uppercase (pure sandbox)
    reverse/              — Reverse bytes (pure sandbox)
    word_count/           — Line/word/byte counter (pure sandbox)
    redact_secret/        — Reads and redacts secrets (IFC demo)
    weather/              — Reads city from secrets, shows wttr.in
    crate_vendor/         — Crate vendoring tool (WASI + HTTP)
  tools/
    generate_policy/      — Policy + manifest + module store generator
  tests/
    integration_test.rs   — End-to-end tests (direct mode + server/client)
```

## Design decisions

### Why categories, not levels?

A linear lattice (Public < Secret < TopSecret) is too coarse. A module trusted
to use the Google Calendar API should not automatically be able to use the
GitHub API. Categories allow **independent** confidentiality concerns.

### Why explicit declassification?

If declassification were automatic (the host strips labels based on policy
whenever the module outputs), then a module exercises its full privilege on
every output whether intended or not. Explicit declassification makes the
security decision **auditable** — you can grep the module source for
`ifc::declassify` calls and see exactly where sensitive data boundaries are
crossed.

### Why a daemon, not a setuid binary?

The cleanroom server needs access to both the network and secret env vars, while
the container (where the human or agent works) must have neither. A daemon on
the host side naturally sits outside the container's network namespace and can
hold secrets the container cannot see. A setuid binary would require the
container to have the secrets in its filesystem (even if permission-restricted),
which is a weaker isolation boundary.

### Why TOML for the policy?

TOML supports comments — critical for a security config file where explaining
_why_ a module has certain privileges is as important as specifying what those
privileges are. JSON doesn't support comments; YAML is ambiguous and
error-prone.
