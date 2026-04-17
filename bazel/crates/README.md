# Oak's Rust Crate Universe Setup

Oak has a large, fairly complicated strategy for managing Rust crates in a way
that meets all of its various build requirements, while working around the
shortcomings of the rules_rust crate_universe system.

## Issues

### Prost-Types Patch

For a detailed explanation of the problem, see
[patched_crates.bzl](patched_crates.bzl).

### Multiple Crate Universes for Multi-Platform Support

Oak builds for multiple platform configurations with different standard library
availability:

- **`oak_std_crates_index`**: For standard builds targeting platforms with full
  `std` support (e.g., `x86_64-unknown-linux-gnu`, `aarch64-apple-darwin`).
- **`oak_no_std_crates_index`**: For `no_std` builds targeting bare-metal or
  Wasm platforms (e.g., `x86_64-unknown-none`, `wasm32-unknown-unknown`). These
  builds disable default features and only enable `no_std`-compatible features
  like `alloc`.
- **`oak_no_std_no_avx_crates_index`**: A variant of `no_std` that also disables
  AVX instructions. This is necessary for certain enclave environments where AVX
  is not available. This is particularly challenging because it's a variant
  _within_ the same platform triple (`x86_64-unknown-none`), not a different
  triple.

Each universe may have the same crate with different feature configurations. For
example, `bytes` has `default_features = True` in `std` but
`default_features = False` in `no_std` builds.

## Conveniences

### Auto-Generated Umbrella Repository to Switch Between Deps and Patches

The `aliasing_crates_repository` (defined in
[aliasing_crates_repository.bzl](aliasing_crates_repository.bzl)) creates a
unified `@oak_crates_index` repository that automatically selects the correct
underlying crate universe based on the current build configuration.

Instead of depending on `@oak_std_crates_index//:tokio` or
`@oak_no_std_crates_index//:bytes` directly, targets depend on
`@oak_crates_index//:crate_name`. The aliasing repository generates `select()`
statements that route to the appropriate underlying repository based on
platform-specific config settings (e.g., `x86_64-none-setting`,
`wasm32-none-setting`).

This also handles crate overrides (like the prost-types patch) transparently, so
consumers don't need to know which crates have special handling.

## Future Improvements

### Prost-Types Patch Fix

rules_rust needs to provide a way to differentiate between host-only targets in
the universe and actual-targets.

### Multiple Crate Universes

rules_rust needs to provide a way to generate selectors for different platform
conditions in the generated build files.
