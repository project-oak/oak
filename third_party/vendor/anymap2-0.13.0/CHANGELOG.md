# 1.0.0 (unreleased)

- Remove `bench` Cargo feature (by shifting benchmarks out of `src/lib.rs` into
  `benches/bench.rs`; it still won’t run on anything but nightly, but that
  don’t signify). Technically a [breaking-change], but it was something for
  development only, so I’m not in the slightest bit concerned by it.

- Implement `Default` on `Map` (not just on `RawMap`)

I don’t plan for there to be any real changes from 0.12.1;
it should be just a bit of housecleaning and a version bump.

# 0.12.1 (2017-01-20)

- Remove superfluous Clone bound on Entry methods (#26)
- Consistent application of `#[inline]` where it should be
- Fix bad performance (see 724f94758def9f71ad27ff49e47e908a431c2728 for details)

# 0.12.0 (2016-03-05)

- Ungate `drain` iterator (stable from Rust 1.6.0)
- Ungate efficient hashing (stable from Rust 1.7.0)
- Remove `unstable` Cargo feature (in favour of a `bench` feature for benchmarking)

# 0.11.2 (2016-01-22)

- Rust warning updates only

# 0.11.1 (2015-06-24)

- Unstable Rust compatibility updates

# 0.11.0 (2015-06-10)

- Support concurrent maps (`Send + Sync` bound)
- Rename `nightly` feature to `unstable`
- Implement `Debug` for `Map` and `RawMap`
- Replace `clone` Cargo feature with arcane DST magicks

# Older releases (from the initial code on 2014-06-12 to 0.10.3 on 2015-04-18)

I’m not giving a changelog for these artefacts of ancient history.
If you really care you can look through the Git history easily enough.
Most of the releases were just compensating for changes to the language
(that being before Rust 1.0; yes, this crate has been around for a while).

I do think that [`src/lib.rs` in the first commit] is a work of art,
a thing of great beauty worth looking at; its simplicity is delightful,
and it doesn’t even need to contain any unsafe code.

[`src/lib.rs` in the first commit]: https://github.com/chris-morgan/anymap/tree/a294948f57dee47bb284d6a3ae1b8f61a902a03c/src/lib.rs
