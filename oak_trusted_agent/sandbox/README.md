# Oak Trusted Agent Sandbox

This directory contains the WebAssembly sandbox guest environment for Oak
Trusted Agents.

The guest runtime compiles TypeScript source code into a WebAssembly Component
Model module adhering to the `oak:agent/agent` interface defined in
`wit/agent.wit`.

## Dependency Management & Hermetic Toolchain

Node.js and npm dependencies are managed hermetically through Bazel using
`aspect_rules_js` and a committed lockfile (`pnpm-lock.yaml`).

- **No host `node_modules`**: Dependencies are fetched, verified by
  cryptographic hash, and cached automatically by Bazel.
- **Reproducible builds**: All package versions and platform binaries (such as
  `esbuild` and `@bytecodealliance/componentize-js`) are pinned with SHA-512
  integrity hashes.
- **Sandboxed compilation**: Build actions execute in Bazel's `linux-sandbox` to
  guarantee deterministic binary hashes for Remote Attestation.

## Updating `pnpm-lock.yaml`

When adding, removing, or bumping dependencies:

1. **Edit `package.json`**: Update dependency versions in
   `oak_trusted_agent/sandbox/package.json`.

   > **Note on `pnpm` configuration in `package.json`**:
   >
   > - `onlyBuiltDependencies`: Packages with native lifecycle/install scripts
   >   (e.g. `esbuild`) must be listed in `pnpm.onlyBuiltDependencies`.
   > - `packageExtensions`: Any missing transitive dependencies (such as
   >   `commander` or `@bytecodealliance/preview2-shim` for `componentize-js`)
   >   must be declared in `pnpm.packageExtensions`.

2. **Regenerate the Lockfile**: From the repository root, run `pnpm` inside the
   Nix development shell:

   ```bash
   nix develop --command bash -c "cd oak_trusted_agent/sandbox && pnpm install --lockfile-only"
   ```

   _The `--lockfile-only` flag updates `pnpm-lock.yaml` with exact hashes
   without downloading packages to a local `node_modules` folder._

3. **Synchronize Bazel Lockfiles**: Update `MODULE.bazel.lock` across all
   workspaces:

   ```bash
   nix develop --command just bazel-lockfile-all
   ```

4. **Verify Formatting & Linting**: Ensure all files are formatted and lockfiles
   are synchronized:

   ```bash
   nix develop --command just format
   ```

## Building

To build the sandbox targets:

```bash
# Build the linked npm package tree
nix develop --command bazel build //oak_trusted_agent/sandbox:node_modules
```
