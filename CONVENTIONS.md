# Conventions in the Oak Repository

This document is a collection of conventions related to package naming,
directory structure, and project organization in the Oak repository.

## Directory Structure

Prefer a hierarchical directory structure.

For example, rather than:

```none
- /oak_containers_attestation
- /oak_containers_orchestrator
- /oak_containers_syslogd
```

Use:

```none
- /oak_containers
  - /attestation
  - /orchestrator
  - /syslogd
```

## Bazel Targets

Do not use `glob("**")`-style patterns in `srcs` attributes for a target. While
this occasionally saves a few keystrokes early on, it's preferable to be very
explicit about the intended source contents of a given target. This makes it
easier to avoid accidentally including unwanted files, and makes it easier to
break things up later on.

This isn't a strict rule: if there's a really good reason for you to use `glob`
somewhere, it's not forbidden. But generally speaking, it doesn't provide much
value, and should be avoided.

## Rust

Oak's primary build system for all languages is Bazel. Cargo is available for
experimental/side projects, but keep in mind that Oak libraries can no longer be
built with Cargo.

### Directories

Conventionally, cargo-based projects use a `src` directory under a crate where
all of the Rust source files lived. This is not strictly needed. Bazel-style
projects should prefer to avoid using a src directory.

#### Testing

For test code, stick to the following conventions:

- Simple unit tests can be directly inline in the relevant file.
  - Remember to create a `rust_test` target to include those tests.

- Larger, more involved tests can be moved to a separate `tests.rs` file,
  optionally prefixed with a descriptor if you have multiple test groups
  (`client_tests.rs`, `server_tests.rs`, etc).

- Complicated, multi-crate integration tests should be in a sub-folder called
  `tests`.

#### Examples

Acceptable layouts:

```none
- my_src_crate
   - src
     - lib.rs
     - support.rs
     - test.rs
   - tests
     - integration_tests.rs
```

```none
- my_flat_crate
  - lib.rs
  - support.rs
  - support_test.rs
  - test.rs
  - tests
    - integration_tests.rs
```

### Crate Naming

Conventionally, the primary crate name in the package should consist of the path
to the BUILD file containing the target, with `/` replaced by `_`.

The `crate_name` attribute is not allowed internally at Google. So avoid using
this attribute on any crates that are intended for internal use. The target name
should be the same as the intended crate name.

It's convenient to have default bazel targets. To enable this convenience, you
can define an alias:

For example, in `oak_containers/orchestrator`:

```python
alias(
    name = "orchestrator",
    actual = ":oak_containers_orchestrator",
)
```

### Crates with Binaries

For crates that have a single `rust_binary` target, use the naming convention
discussed above.

If your package exposes a library along with a crate, prefer to use the crate
name as the name of the library target. The primary `rust_binary` target can
simply be called `bin/crate_name` - the generated output will be a a `bin`
subdirectory, but using the crate name.

Unless there's a very good reason, stick with using the library as the package
default target alias, and refer to the binary rule usin the `:bin/crate_name`
target.
