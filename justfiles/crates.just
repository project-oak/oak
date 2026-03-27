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

# Show dependency tree for a crate to understand why it's included.
[doc("Show full dependency info for a crate in the lock file.
Shows dependents (reverse deps), dependencies (forward deps), and
all paths from root crates to the target.

Examples:
    just crates deps serde          # direct dependents + deps
    just crates deps serde 3        # 3 levels deep in both directions
    just crates deps ring 2         # debug multi-version pulls
")]
deps crate depth="1":
    #!/usr/bin/env bash
    set -euo pipefail
    (cd tools/analyze_crate_versions && bazel build //:analyze_crate_versions)
    exec tools/analyze_crate_versions/bazel-bin/analyze_crate_versions --deps={{crate}} --depth={{depth}}