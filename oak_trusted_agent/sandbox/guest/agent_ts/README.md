# Oak Trusted Agent TypeScript Guest

TypeScript agent built on ADK and compiled with `componentize-js` into a
WebAssembly component (`:adk_agent_ts`) that implements the `oak:agent` world
defined in [`../../wit/agent.wit`](../../wit/agent.wit).

The TypeScript ambient declarations in `src/types.d.ts` are generated from the
WIT interface and checked by `:wit_types_sync_test`. Regenerate them with:

```bash
nix develop --command bazel run //oak_trusted_agent/sandbox/guest/agent_ts:generate_wit_types
```

## Hermetic npm toolchain

Node.js and npm dependencies are managed through Bazel using `aspect_rules_js`
and `pnpm-lock.yaml`:

- Dependencies are fetched, checked by cryptographic hash, and cached by Bazel
  without a host `node_modules` tree.
- Package versions and platform binaries (`esbuild` and
  `@bytecodealliance/componentize-js`) are pinned with SHA-512 integrity hashes.
- Build actions run inside Bazel's `linux-sandbox` so output Wasm hashes are
  reproducible.

## Updating `pnpm-lock.yaml`

When adding, removing, or bumping dependencies:

1. Update dependency versions in
   `oak_trusted_agent/sandbox/guest/agent_ts/package.json`.
   - Packages with native lifecycle/install scripts (`esbuild`) must be listed
     in `pnpm.onlyBuiltDependencies`.
   - Missing transitive dependencies (`commander` or
     `@bytecodealliance/preview2-shim` for `componentize-js`) must be declared
     in `pnpm.packageExtensions`.

2. Regenerate `pnpm-lock.yaml` from the repository root without populating a
   local `node_modules` directory:

   ```bash
   nix develop --command bash -c "cd oak_trusted_agent/sandbox/guest/agent_ts && pnpm install --lockfile-only"
   ```

3. Update `MODULE.bazel.lock` across all workspaces:

   ```bash
   nix develop --command just bazel-lockfile-all
   ```

4. Format modified files and check lockfiles:

   ```bash
   nix develop --command just format
   ```

## Building

```bash
nix develop --command bazel build //oak_trusted_agent/sandbox/guest/agent_ts:node_modules
nix develop --command bazel build //oak_trusted_agent/sandbox/guest/agent_ts:adk_agent_ts
```
