# `analyze_crate_versions`

A developer tool that analyzes the Rust dependencies in the repository by
comparing the versions requested in the Bazel configuration against the actual
resolved versions in the Bazel lockfile, and the latest published versions
available on [crates.io](https://crates.io).

This tool helps keep track of stale dependencies, visualizes update availability
(Patch, Minor, Major), and highlights crates that haven't received updates in a
long time.

## Usage

```bash
bazel run -- [OPTIONS] [LOCK_FILE]

or use the recipe shortcut:

just crates versions
```

### Arguments and Flags

- `[LOCK_FILE]`: Path to the Bazel lockfile to parse. Defaults to
  `MODULE.bazel.lock` in the current directory if omitted.
- `-f, --filter <STRING>`: Filter the report by crate name using a substring
  match.
- `-u, --update`: Force an update by fetching the latest crate information from
  crates.io (bypassing the local cache).
- `--include-pre-release`: Include pre-release versions when displaying the
  Latest versions and calculating updates.
- `--versions-file <PATH>`: Path to a custom versions cache JSON file. Defaults
  to `~/.cache/oak/crate_cache.json`.

## Understanding the Report

The terminal output provides a table with the following columns:

- **Crate**: The name of the crate dependency.
- **Req**: The version explicitly requested in `MODULE.bazel`.
- **Act**: The actual version resolved and installed according to the lockfile.
  Multiple rows are displayed if multiple versions of a crate are resolved.
- **Latest(P)**: The highest available **Patch** update.
- **Latest(m)**: The highest available **Minor** update.
- **Latest(M)**: The highest available **Major** update.
- **Usage**: The number of times the crate is explicitly used or referenced
  across the codebase.
- **Latest Date**: The publish date of the most recent version of the crate.
  - Colors highlight crates that might be unmaintained:
    - **Yellow**: The latest publish date is older than 2 years.
    - **Red**: The latest publish date is older than 3 years.

A dash (`-`) in the update columns indicates that no update of that specific
type is available (e.g., if you are already on the latest patch).

## Caching

To rapidly generate reports without repeatedly querying `crates.io`, the tool
caches the API responses locally in `~/.cache/oak/crate_cache.json`. Run the
tool with `-u` / `--update` periodically to refresh this cache.
