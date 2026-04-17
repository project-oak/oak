# Cleanroom

**A sandboxed WebAssembly runner with Information Flow Control (IFC) for humans
and LLM agents.**

Cleanroom executes Wasm modules in a secure environment with fine-grained
tracking of data secrecy and integrity. Modules interact via standard WASI,
while the host silently tracks which secrets each module has accessed (secrecy)
and who vouches for the data (integrity), enforcing declassification and
endorsement policies before allowing data to cross trust boundaries.

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
entry.

Inside the shell you can run modules:

```console
$ echo "hello world" | cleanroom run to_uppercase_wasm
HELLO WORLD

$ cleanroom run redact_secret_wasm --secrecy=caller,secret_category --integrity=caller
Redacted secret: top-**********

# Running with an insufficient secrecy label produces an error.
$ cleanroom run redact_secret_wasm --integrity=caller
[2026-04-10T12:11:41Z WARN  cleanroom_lib::wasi_ifc] cell read denied: "secret_api_key" with label (S={secret_category}, I={caller}) does not flow to computation label (S={caller}, I={caller}): excess secrecy: [secret_category]
Error: Custom { kind: Other, error: "Could not read secret_api_key from cell" }

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

IFC tracks **which sensitive data a module has seen** (secrecy) and **who
vouches for the computation** (integrity), blocking output to channels that
shouldn't receive that data.

### Labels

Each resource carries a dual-component **label** — a pair `(secrecy, integrity)`
where both components are sets of [principals](#principals). This follows the
[Decentralized Label Model (DLM)][dlm].

- **Secrecy**: more principals = more restricted. Data labeled `{github, tzn}`
  requires authority over _both_ to declassify.
- **Integrity**: more principals = more trusted. Data vouched for by `{github}`
  is higher-integrity than unsigned data.

[dlm]: https://www.cs.cornell.edu/andru/papers/iflow-sosp97/

| Resource               | Secrecy              | Integrity  |
| ---------------------- | -------------------- | ---------- |
| Cell: `github_api_key` | `{github, tzn}`      | `{github}` |
| Cell: `user_location`  | `{user_location}`    | `∅`        |
| HTTP (public internet) | `∅`                  | `∅`        |
| Agent stdin/stdout     | `{caller_principal}` | `∅`        |

The data cell configuration file defines both dimensions:

```toml
[[cell]]
name      = "github_api_key"
value     = "ghp_xxx"
secrecy   = ["github", "tzn"]
integrity = ["github"]
```

### Principals

A **principal** is the atom of both lattice dimensions — it represents an
identity that can own secrecy tags and vouch for integrity. There are three
kinds, managed in `principals.toml`:

| Kind    | Example           | Identified by       |
| ------- | ----------------- | ------------------- |
| Named   | `tzn`, `github`   | Human-readable name |
| SSH key | `tzn_key`         | Base64 public key   |
| Module  | `crate_vendor_v1` | Wasm content digest |

Delegation is explicit via **speaks-for** edges. For example, an SSH key
`tzn_key` speaks for the named principal `tzn`. The server resolves transitive
delegations to determine a caller's full authority.

### Computation label

The host assigns a **fixed** dual-component label at module spawn time from the
caller's `--secrecy` and `--integrity` flags. Cell reads are **access-checked**
against this label — no implicit taint raising.

```text
label = (S={caller, calendar_token}, I={caller})   ← declared at spawn
  module reads google_oauth_token cell
  check: {calendar_token} ⊆ {caller, calendar_token} ✓
label unchanged                                  ← fixed, not raised
```

### Flow rule

Data at label `L₁` can flow to a channel at label `L₂` iff:

- `L₁.secrecy ⊆ L₂.secrecy` (no write-down)
- `L₂.integrity ⊆ L₁.integrity` (no read-down)

### Privilege: declassification and endorsement

Modules carry a [`Privilege`](src/ifc.rs) derived from the `speaks_for` edges in
the policy file. A module's `speaks_for` set determines its full privilege:

- **Declassify**: remove secrecy principals it speaks for.
- **Endorse**: restore integrity principals it speaks for.

Both operations are **explicit** — the module must call them at a specific point
in its code. This makes security decisions auditable.

### What modules see

Modules use **standard WASI** for all I/O. The only IFC-specific APIs are
optional host imports:

```text
ifc::get_label()       → current secrecy principals
ifc::declassify(ps)    → remove secrecy principals (privilege-checked)
ifc::get_cell(name)    → read labeled data cell (access-checked against label)
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

| Property          | Direct mode | Server/client mode                    |
| ----------------- | ----------- | ------------------------------------- |
| Filesystem access | ❌ None     | ✅ Via custom FS ABI (IFC-gated)      |
| Network access    | ❌ None     | ✅ Via custom HTTP ABI (IFC-gated)    |
| Secrets           | ❌ None     | ✅ Labeled data cells / env vars      |
| IFC enforcement   | ❌ No       | ✅ Dual-component (secrecy+integrity) |
| Identity          | ❌ No       | ✅ Principal-based trust graph        |
| Fuel / CPU budget | ✅ wasmtime | ✅ wasmtime                           |
| Memory budget     | ✅ wasmtime | ✅ wasmtime                           |
| Network isolation | N/A         | ✅ `sandbox-exec` / `--network=none`  |

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
bazel run //cleanroom/tools/generate_policy

# Terminal 1 — start the server
bazel run //cleanroom -- server \
  --policy-file=cleanroom/example_policy.toml \
  --cells-file=cleanroom/example_cells.toml \
  --socket=/tmp/cleanroom.sock \
  --module-store=/tmp/modules

# Terminal 2 — run a module with a label
export CLEANROOM_SOCKET=/tmp/cleanroom.sock
echo "hello world" | bazel run //cleanroom -- run \
  to_uppercase_wasm --integrity=tzn --secrecy=tzn

# Terminal 2 — run a module that needs access to secret cells
echo "user@gmail.com" | bazel run //cleanroom -- run \
  limited_calendar_wasm \
  --integrity=caller --secrecy=caller,calendar_token
```

The `--integrity` flag identifies the caller (who vouches for stdin). The
`--secrecy` flag sets the secrecy categories for the computation. The module
must be authorized (via `speaks_for`) for every secrecy principal beyond the
caller's own identity.

## Examples

| Module             | Source                                                     | Description                            |
| ------------------ | ---------------------------------------------------------- | -------------------------------------- |
| `to_uppercase`     | [`examples/to_uppercase/`](examples/to_uppercase/)         | ASCII uppercase                        |
| `reverse`          | [`examples/reverse/`](examples/reverse/)                   | Reverse bytes                          |
| `word_count`       | [`examples/word_count/`](examples/word_count/)             | Count lines/words/bytes (like `wc`)    |
| `redact_secret`    | [`examples/redact_secret/`](examples/redact_secret/)       | Reads and redacts secrets (IFC demo)   |
| `weather`          | [`examples/weather/`](examples/weather/)                   | Reads city from secrets, shows wttr.in |
| `crate_vendor`     | [`examples/crate_vendor/`](examples/crate_vendor/)         | Vendored crate downloads               |
| `limited_calendar` | [`examples/limited_calendar/`](examples/limited_calendar/) | Google Calendar with IFC + HTTP        |

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
  example_policy.toml     — Trust graph: principals + speaks-for
                            (generated by tools/generate_policy)
  example_cells.toml      — Data cells with secrecy + integrity labels
  secrets/                — Example secrets directory (IFC-labeled)
  src/
    main.rs               — Entry point: run, server, client, shell, principal
    ifc.rs                — IFC types: Label (secrecy+integrity), Privilege
                            (declassify+endorse), ComputationLabel, FlowError
    principals.rs         — Trust graph parser: Named/SSH/Module
                            principals, speaks-for delegation
    policy.rs             — Cells parser (TOML)
    protocol.rs           — RPC protocol (bincode over Unix socket)
    server.rs             — Host-side IFC server daemon (identity-aware)
    client.rs             — Thin client for inside the container
    shell.rs              — Sandboxed shell launcher (sandbox-exec / Docker)
    wasi_ifc.rs           — WASI interception for IFC enforcement
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

### Why principals, not levels?

A linear lattice (Public < Secret < TopSecret) is too coarse. A module trusted
to use the Google Calendar API should not automatically be able to use the
GitHub API. Principals allow **independent** secrecy and integrity concerns, and
tie labels to real identities.

### Why dual-component labels?

Secrecy alone isn't enough for [robust declassification][robust]. Without
integrity tracking, an attacker-influenced module could steer _what_ gets
declassified. By tracking integrity alongside secrecy, the system can gate
declassification on whether the computation was influenced by trusted data only.
This follows the DLM/DIFC model used in Flume, HiStar, and JIF.

[robust]: https://www.cis.upenn.edu/~stevez/papers/ZM01b.pdf

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
