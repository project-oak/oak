set working-directory := '..'

# Recipes for dealing with Rust crates

[private]
default:
    @just --list crates

# Analyze crate versions: compare requested vs actual vs latest on crates.io.
[doc("Run the crate version analyzer.
Shows a report of all crate versions, available updates, and usage counts.

Examples:
    just crates versions              # full report
    just crates versions -f serde     # filter by name
    just crates versions -u           # force refresh cache
")]
versions *ARGS:
    #!/usr/bin/env bash
    set -euo pipefail
    (cd tools/analyze_crate_versions && bazel build //:analyze_crate_versions)
    exec tools/analyze_crate_versions/bazel-bin/analyze_crate_versions {{ARGS}}