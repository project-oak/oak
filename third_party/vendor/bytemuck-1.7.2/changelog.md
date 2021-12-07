# `bytemuck` changelog

## 1.7.2

* Why does this repo keep being hit with publishing problems? What did I do to
  deserve this curse, Ferris? This doesn't ever happen with tinyvec or fermium,
  only bytemuck.

## 1.7.1

* **Soundness Fix:** The wrap/peel methods for owned value conversion, added to
  `TransparentWrapper` in 1.6, can cause a double-drop if used with types that
  impl `Drop`. The fix was simply to add a `ManuallyDrop` layer around the value
  before doing the `transmute_copy` that is used to wrap/peel. While this fix
  could technically be backported to the 1.6 series, since 1.7 is semver
  compatible anyway the 1.6 series has simply been yanked.

## 1.7

* In response to [Unsafe Code Guidelines Issue
  #286](https://github.com/rust-lang/unsafe-code-guidelines/issues/286), this
  version of Bytemuck has a ***Soundness-Required Breaking Change***. This is
  "allowed" under Rust's backwards-compatibility guidelines, but it's still
  annoying of course so we're trying to keep the damage minimal.
  * **The Reason:** It turns out that pointer values should not have been `Pod`. More
    specifically, `ptr as usize` is *not* the same operation as calling
    `transmute::<_, usize>(ptr)`.
  * LLVM has yet to fully sort out their story, but until they do, transmuting
    pointers can cause miscompilations. They may fix things up in the future,
    but we're not gonna just wait and have broken code in the mean time.
  * **The Fix:** The breaking change is that the `Pod` impls for `*const T`,
    `*mut T`, and `Option<NonNull<T>` are now gated behind the
    `unsound_ptr_pod_impl` feature, which is off by default.
  * You are *strongly discouraged* from using this feature, but if a dependency
    of yours doesn't work when you upgrade to 1.7 because it relied on pointer
    casting, then you might wish to temporarily enable the feature just to get
    that dependency to build. Enabled features are global across all users of a
    given semver compatible version, so if you enable the feature in your own
    crate, your dependency will also end up getting the feature too, and then
    it'll be able to compile.
  * Please move away from using this feature as soon as you can. Consider it to
    *already* be deprecated.
  * [PR 65](https://github.com/Lokathor/bytemuck/pull/65)

## 1.6.3

* Small goof with an errant `;`, so [PR 69](https://github.com/Lokathor/bytemuck/pull/69)
  *actually* got things working on SPIR-V.

## 1.6.2

cargo upload goof! ignore this one.

## 1.6.1

* [DJMcNab](https://github.com/DJMcNab) did a fix so that the crate can build for SPIR-V
  [PR 67](https://github.com/Lokathor/bytemuck/pull/67)

## 1.6

* The `TransparentWrapper` trait now has more methods. More ways to wrap, and
  now you can "peel" too! Note that we don't call it "unwrap" because that name
  is too strongly associated with the Option/Result methods.
  Thanks to [LU15W1R7H](https://github.com/LU15W1R7H) for doing
  [PR 58](https://github.com/Lokathor/bytemuck/pull/58)
* Min Const Generics! Now there's Pod and Zeroable for arrays of any size when
  you turn on the `min_const_generics` crate feature.
  [zakarumych](https://github.com/zakarumych) got the work started in
  [PR 59](https://github.com/Lokathor/bytemuck/pull/59),
  and [chorman0773](https://github.com/chorman0773) finished off the task in
  [PR 63](https://github.com/Lokathor/bytemuck/pull/63)

## 1.5.1

* Fix `bytes_of` failing on zero sized types.
  [PR 53](https://github.com/Lokathor/bytemuck/pull/53)

## 1.5

* Added `pod_collect_to_vec`, which will gather a slice into a vec,
allowing you to change the pod type while also safely ignoring alignment.
[PR 50](https://github.com/Lokathor/bytemuck/pull/50)

## 1.4.2

* [Kimundi](https://github.com/Kimundi) fixed an issue that could make `try_zeroed_box`
stack overflow for large values at low optimization levels.
[PR 43](https://github.com/Lokathor/bytemuck/pull/43)

## 1.4.1

* [thomcc](https://github.com/thomcc) fixed up the CI and patched over a soundness hole in `offset_of!`.
[PR 38](https://github.com/Lokathor/bytemuck/pull/38)

## 1.4

* [icewind1991](https://github.com/icewind1991) has contributed the proc-macros
  for deriving impls of `Pod`, `TransparentWrapper`, `Zeroable`!! Everyone has
  been waiting for this one folks! It's a big deal. Just enable the `derive`
  cargo feature and then you'll be able to derive the traits on your types. It
  generates all the appropriate tests for you.
* The `zeroable_maybe_uninit` feature now adds a `Zeroable` impl to the
  `MaybeUninit` type. This is only behind a feature flag because `MaybeUninit`
  didn't exist back in `1.34.0` (the minimum rust version of `bytemuck`).

## 1.3.1

* The entire crate is now available under the `Apache-2.0 OR MIT` license as
  well as the previous `Zlib` license
  [#24](https://github.com/Lokathor/bytemuck/pull/24).
* [HeroicKatora](https://github.com/HeroicKatora) added the
  `try_zeroed_slice_box` function
  [#10](https://github.com/Lokathor/bytemuck/pull/17). `zeroed_slice_box` is
  also available.
* The `offset_of!` macro now supports a 2-arg version. For types that impl
  Default, it'll just make an instance using `default` and then call over to the
  3-arg version.
* The `PodCastError` type now supports `Hash` and `Display`. Also if you enable
  the `extern_crate_std` feature then it will support `std::error::Error`.
* We now provide a `TransparentWrapper<T>` impl for `core::num::Wrapper<T>`.
* The error type of `try_from_bytes` and `try_from_bytes_mut` when the input
  isn't aligned has been corrected from being `AlignmentMismatch` (intended for
  allocation casting only) to `TargetAlignmentGreaterAndInputNotAligned`.

## 1.3.0

* Had a bug because the CI was messed up! It wasn't soundness related, because
  it prevented the crate from building entirely if the `extern_crate_alloc`
  feature was used. Still, this is yanked, sorry.

## 1.2.0

* [thomcc](https://github.com/thomcc) added many things:
  * A fully sound `offset_of!` macro
    [#10](https://github.com/Lokathor/bytemuck/pull/10)
  * A `Contiguous` trait for when you've got enums with declared values
    all in a row [#12](https://github.com/Lokathor/bytemuck/pull/12)
  * A `TransparentWrapper` marker trait for when you want to more clearly
    enable adding and removing a wrapper struct to its inner value
    [#15](https://github.com/Lokathor/bytemuck/pull/15)
  * Now MIRI is run on CI in every single push!
    [#16](https://github.com/Lokathor/bytemuck/pull/16)

## 1.1.0

* [SimonSapin](https://github.com/SimonSapin) added `from_bytes`,
  `from_bytes_mut`, `try_from_bytes`, and `try_from_bytes_mut` ([PR
  Link](https://github.com/Lokathor/bytemuck/pull/8))

## 1.0.1

* Changed to the [zlib](https://opensource.org/licenses/Zlib) license.
* Added much more proper documentation.
* Reduced the minimum Rust version to 1.34
