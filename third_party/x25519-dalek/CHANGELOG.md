# Changelog

Entries are listed in reverse chronological order.

# 1.x Series

## 1.2

* Add module documentation for using the bytes-oriented `x25519()` API.
* Add implementation of `zeroize::Zeroize` for `PublicKey`.
* Move unittests to a separate directory.
* Add cargo feature flags `"fiat_u32_backend"` and `"fiat_u64_backend"` for
  activating the Fiat crypto field element implementations.
* Fix issue with removed `feature(external_doc)` on nightly compilers.
* Pin `zeroize` to version 1.3 to support a wider range of MSRVs.
* Add CI via Github actions.
* Fix breakage in the serde unittests.
* MSRV is now 1.41 for production and 1.48 for development.
* Add an optional check to `SharedSecret` for contibutory behaviour.
* Add implementation of `ReusableSecret` keys which are non-ephemeral, but which
  cannot be serialised to discourage long-term use.

## 1.1.1

* Fix a typo in the README.

## 1.1.0

* Add impls of `PartialEq`, `Eq`, and `Hash` for `PublicKey` (by @jack-michaud)

## 1.0.1

* Update underlying `curve25519_dalek` library to `3.0`.

## 1.0.0

* Widen generic bound on `EphemeralSecret::new` and `StaticSecret::new` to
  allow owned as well as borrowed RNGs.
* Add `PublicKey::to_bytes` and `SharedSecret::to_bytes`, returning owned byte
  arrays, complementing the existing `as_bytes` methods returning references.
* Remove mention of deprecated `rand_os` crate from examples.
* Clarify `EphemeralSecret`/`StaticSecret` distinction in documentation.

# Pre-1.0.0

## 0.6.0

* Updates `rand_core` version to `0.5`.
* Adds `serde` support.
* Replaces `clear_on_drop` with `zeroize`.
* Use Rust 2018.

## 0.5.2

* Implement `Clone` for `StaticSecret`.

## 0.5.1

* Implement `Copy, Clone, Debug` for `PublicKey`.
* Remove doctests.

## 0.5.0

* Adds support for static and ephemeral keys.

