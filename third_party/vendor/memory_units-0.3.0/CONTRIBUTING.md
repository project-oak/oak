# Contributing to `memory_units`

Hi! We'd love to have your contributions! If you want help or mentorship, reach
out to us in a GitHub issue, or ping `pepyakin` or `fitzgen` in
[`#rust` on `irc.mozilla.org`](irc://irc.mozilla.org#rust-wasm) and introduce
yourself.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [Code of Conduct](#code-of-conduct)
- [Building and Testing](#building-and-testing)
  - [Building](#building)
  - [Testing](#testing)
- [Automatic Code Formatting](#automatic-code-formatting)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Code of Conduct

We abide by the [Rust Code of Conduct][coc] and ask that you do as well.

[coc]: https://www.rust-lang.org/en-US/conduct.html

## Building and Testing

### Building

```
$ cargo build
```

### Testing

```
$ cargo test
```

## Automatic Code Formatting

We use [`rustfmt`](https://github.com/rust-lang-nursery/rustfmt) to enforce a
consistent code style across the whole code base.

You can install the latest version of `rustfmt` with this command:

```
$ rustup update
$ rustup component add rustfmt-preview
```

Ensure that `~/.rustup/toolchains/$YOUR_HOST_TARGET/bin/` is on your `$PATH`.

Once that is taken care of, you can (re)format all code by running this command
from the root of the repository:

```
$ cargo fmt --all
```
