# Gemini Instructions

## Building and Running

This project contains source files written in a variety of languages, mostly
Rust, all managed via Bazel.

Do not attempt to build anything with Cargo. There are some Cargo related files
around, but they are not expected to work.

The project uses `just` to provide useful commands for developers and CI. Look
into the `justfile` to see a few example recipes. Feel free to call `just`
directly, or look at how some of those recipes are defined, and do something
similar yourself (e.g. by running `bazel` directly in similar ways).

## Writing Code

After editing files, please run `just format` - at least once, at the end of
completing all edits - to format the code appropriately.

## API Design

When writing new APIs follow the guidelines:

- Write extensive doc comments explaining the intended use of all parts of the
  APIs and the interaction between the components
- Design for testability: make sure all dependencies can be replaced by mocks
  for testing, where possible create appropriate mocks
- The APIs should be safe:
  - Avoid using `unsafe` code
  - When handling cryptographic primitives don't create unnecessary copies of
    private keys
  - Don't keep the keys in memory when they are no longer in use
  - Make it hard for the API users to do unsafe things. For example don't return
    raw private keys to the caller, instead create a handler with intended
    operations for them to use
- Utilize structured errors (such as provided by `thiserror`) to provide
  sufficient context to the API callers
- APIs should utilize the type system to make invalid states unrepresentable

## Writing Tests

This project uses `googletest` whenever possible for both C++ and Rust tests.

While `just build-and-test` is available to run all tests, it can be slow. For a
faster, more targeted approach, you can run tests for a specific package using
`bazel test //path/to/package:all`. For example, to run only the tests for the
`oak_time` crate, use `bazel test //oak_time:all`.

If a target does not have any tests, running `bazel test` on it will fail. In
this case, use `bazel build` to verify the target instead.

Note: The following two test targets are expected to fail when running
`just build-and-test` in the local development environment. This is known
behavior and can be disregarded:

- `//oak_containers/examples/hello_world/host_app:oak_containers_hello_world_host_app_tests_tests/integration_test_test`
- `//oak_functions_containers_launcher:oak_functions_containers_launcher_test_tests/integration_test_test`

## Rust

If possible, Rust code should be compatible with `no_std`. Many of the traits
and structs in `std` are also found in `core` and / or `alloc`, and those are
usually fine to use everywhere. Try to use the most precise version.

Tests usually need `std` to run, so if you create a module with testing helpers,
make sure you gate that behind `#[cfg(test)]`, so it only gets built when
testing, otherwise it will probably drag `std` into the main (non-test) build
and break that.

## Working with Protobufs

The project's protobuf files are located in the `proto` directory. After
modifying any of these files, you must run the following command to regenerate
the corresponding Rust code:

```bash
bazel run oak_proto_rust:copy_generated_files
```

## Adding Crate Dependencies

To add a new crate dependency to the project, you need to:

1. **Add the crate to `bazel/crates/oak_crates.bzl`**. Be mindful of the
   following:
   - **Dependency Group:** Add the crate to the appropriate dictionary.
     - `_common_crates`: For crates that are used in both `std` and `no_std`
       environments.
     - `OAK_NO_STD_CRATES`: For crates that are only used in `no_std`
       environments.
     - `OAK_STD_CRATES`: For crates that are only used in `std` environments.
   - **Features:** Carefully select the features for each crate. For `no_std`
     builds, it's critical to set `default_features = False` and only enable the
     features that are compatible with a `no_std` environment (e.g., `alloc`).
2. **Run `just bazel-repin-all`** to update the lockfiles and BUILD files.

## Documentation

If you learn anything new about the codebase, please update this file with those
details.

## Style Guide

- Do not use the word "learning". Use "lesson" instead.

### Errors

Add `context("message")` to errors when it reduces ambiguity. Higher up in the
stack, use a `message` that starts with a verb and use gerund. Fine to repeat a
human readable version of the function name the context is attached to. Negative
terms like "fail" or "missing" should only be used in actual errors at the
deepest level. Don't be too verbose in these context messages.

Examples:

```rust
verify_signature(evidence).context("verifying signature")?;
let timestamp = request.timestamp.as_ref().context("missing timestamp")?;
```

## Git

We don't use git.

Do not run any git commands, not even `git status`, and definitely not
`git commit`, `git push` or `git checkout`.

### Commits

- When writing commit messages, any backticks
  (`) must be escaped with a backslash (\`) to ensure they are correctly
  written.
