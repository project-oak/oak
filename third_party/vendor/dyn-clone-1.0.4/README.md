Clone trait that is object-safe
===============================

[<img alt="github" src="https://img.shields.io/badge/github-dtolnay/dyn--clone-8da0cb?style=for-the-badge&labelColor=555555&logo=github" height="20">](https://github.com/dtolnay/dyn-clone)
[<img alt="crates.io" src="https://img.shields.io/crates/v/dyn-clone.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/dyn-clone)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-dyn--clone-66c2a5?style=for-the-badge&labelColor=555555&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/dyn-clone)
[<img alt="build status" src="https://img.shields.io/github/workflow/status/dtolnay/dyn-clone/CI/master?style=for-the-badge" height="20">](https://github.com/dtolnay/dyn-clone/actions?query=branch%3Amaster)

This crate provides a `DynClone` trait that can be used in trait objects, and a
`clone_box` function that can clone any sized or dynamically sized
implementation of `DynClone`. Types that implement the standard library's
[`std::clone::Clone`] trait are automatically usable by a `DynClone` trait
object.

[`std::clone::Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html

The signature of `clone_box` is:

```rust
fn clone_box<T>(t: &T) -> Box<T>
where
    T: ?Sized + DynClone
```

## Example

```rust
use dyn_clone::DynClone;

trait MyTrait: DynClone {
    fn recite(&self);
}

impl MyTrait for String {
    fn recite(&self) {
        println!("{} ♫", self);
    }
}

fn main() {
    let line = "The slithy structs did gyre and gimble the namespace";

    // Build a trait object holding a String.
    // This requires String to implement MyTrait and std::clone::Clone.
    let x: Box<dyn MyTrait> = Box::new(String::from(line));

    x.recite();

    // The type of x2 is a Box<dyn MyTrait> cloned from x.
    let x2 = dyn_clone::clone_box(&*x);

    x2.recite();
}
```

This crate includes a macro for generating the implementation `impl
std::clone::Clone for Box<dyn MyTrait>` in terms of `dyn_clone::clone_box`:

```rust
// As before.
trait MyTrait: DynClone {
    /* ... */
}

dyn_clone::clone_trait_object!(MyTrait);

// Now data structures containing Box<dyn MyTrait> can derive Clone:
#[derive(Clone)]
struct Container {
    trait_object: Box<dyn MyTrait>,
}
```

Check out the [dyn-clonable] crate which provides the same Clone impl for
`Box<dyn MyTrait>` in a more concise attribute form.

[dyn-clonable]: https://github.com/kardeiz/objekt-clonable

<br>

#### License

<sup>
Licensed under either of <a href="LICENSE-APACHE">Apache License, Version
2.0</a> or <a href="LICENSE-MIT">MIT license</a> at your option.
</sup>

<br>

<sub>
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
</sub>
