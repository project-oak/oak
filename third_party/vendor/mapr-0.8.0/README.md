# mapr

> Fork of the great [memmap](https://github.com/danburkert/memmap-rs) library.

A Rust library for cross-platform memory mapped IO.

[![Documentation](https://docs.rs/mapr/badge.svg)](https://docs.rs/mapr)
[![Crate](https://img.shields.io/crates/v/mapr.svg)](https://crates.io/crates/mapr)

## Features

- [x] file-backed memory maps
- [x] anonymous memory maps
- [x] synchronous and asynchronous flushing
- [x] copy-on-write memory maps
- [x] read-only memory maps
- [x] stack support (`MAP_STACK` on unix)
- [x] executable memory maps
- [ ] huge page support

## Platforms

`mapr` should work on any platform supported by
[`libc`](https://github.com/rust-lang-nursery/libc#platforms-and-documentation).
`mapr` requires Rust stable 1.13 or greater.

`mapr` is continuously tested on:
  * `x86_64-unknown-linux-gnu` (Linux)
  * `i686-unknown-linux-gnu`
  * `x86_64-unknown-linux-musl` (Linux MUSL)
  * `x86_64-apple-darwin` (OSX)
  * `i686-apple-darwin`
  * `x86_64-pc-windows-msvc` (Windows)
  * `i686-pc-windows-msvc`
  * `x86_64-pc-windows-gnu`
  * `i686-pc-windows-gnu`

`mapr` is continuously cross-compiled against:
  * `arm-linux-androideabi` (Android)
  * `aarch64-unknown-linux-gnu` (ARM)
  * `arm-unknown-linux-gnueabihf`
  * `mips-unknown-linux-gnu` (MIPS)
  * `x86_64-apple-ios` (iOS)
  * `i686-apple-ios`

## License

`mapr` is primarily distributed under the terms of both the MIT license and the
Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE), [LICENSE-MIT](LICENSE-MIT) for details.

Copyright (c) 2015 Dan Burkert.
