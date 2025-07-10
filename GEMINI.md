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

## Writing Tests

This project uses `googletest` whenever possible for both C++ and Rust tests.

## Rust

If possible, Rust code should be compatible with `no_std`. Many of the traits
and structs in `std` are also found in `core` and / or `alloc`, and those are
usually fine to use everywhere. Try to use the most precise version.

Tests usually need `std` to run, so if you create a module with testing helpers,
make sure you gate that behind `#[cfg(test)]`, so it only gets built when
testing, otherwise it will probably drag `std` into the main (non-test) build
and break that.
