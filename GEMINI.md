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
