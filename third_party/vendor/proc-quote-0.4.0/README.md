Rust Quasiquoter
==================

[![Build Status](https://travis-ci.org/Goncalerta/proc-quote.svg?branch=master)](https://travis-ci.org/Goncalerta/proc-quote)
[![Latest Version](https://img.shields.io/crates/v/proc-quote.svg)](https://crates.io/crates/proc-quote)
[![Rust Documentation](https://img.shields.io/badge/api-rustdoc-blue.svg)](https://docs.rs/proc-quote/0/proc_quote/macro.quote.html)

This crate implements the [`quote!`] macro as a procedural macro, instead of 
[the original `quote!` macro](https://github.com/dtolnay/quote), implemented 
with `macro_rules!`.

The [`quote!`] macro turns Rust syntax tree data structures into tokens of 
source code.

[`quote!`]: https://docs.rs/proc-quote/0/proc_quote/macro.quote.html
[`quote_spanned!`]: https://docs.rs/proc-quote/0/proc_quote/macro.quote_spanned.html

Procedural macros in Rust receive a stream of tokens as input, execute arbitrary
Rust code to determine how to manipulate those tokens, and produce a stream of
tokens to hand back to the compiler to compile into the caller's crate.
Quasi-quoting is a solution to one piece of that -- producing tokens to return
to the compiler.

The idea of quasi-quoting is that we write *code* that we treat as *data*.
Within the `quote!` macro, we can write what looks like code to our text editor
or IDE. We get all the benefits of the editor's brace matching, syntax
highlighting, indentation, and maybe autocompletion. But rather than compiling
that as code into the current crate, we can treat it as data, pass it around,
mutate it, and eventually hand it back to the compiler as tokens to compile into
the macro caller's crate.

This crate is motivated by the procedural macro use case, but it is a general-purpose 
Rust quasi-quoting library and is not specific to procedural macros.

## From `quote` to `proc-quote`

This crate serves the same purpose as [`quote`](https://crates.io/crates/quote)
however it is implemented with procedural macros rather than `macro_rules!`. Switching 
from `quote` to the `proc_quote` crate **should not require any change in the code**.

After changing your `Cargo.toml` dependency, change the following:
```rust
extern crate quote;
use quote::quote;
use quote::quote_spanned;
```
respectively into:
```rust
extern crate proc_quote;
use proc_quote::quote;
use proc_quote::quote_spanned;
```

And that's it!

[`Repeat`]: https://docs.rs/proc-quote/0/proc_quote/trait.Repeat.html
[`Iterator<T>`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
[`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
[`ToTokens`]: https://docs.rs/proc-quote/0/proc_quote/trait.ToTokens.html
[`IntoIterator`]: https://doc.rust-lang.org/std/iter/trait.IntoIterator.html


## Syntax

The quote crate provides a `quote!` macro within which you can write Rust code
that gets packaged into a [`TokenStream`] and can be treated as data. You should
think of `TokenStream` as representing a fragment of Rust source code.

[`TokenStream`]: https://docs.rs/proc-macro2/0/proc_macro2/struct.TokenStream.html

Within the `quote!` macro, interpolation is done with `#var`. Any type
implementing the [`quote::ToTokens`] trait can be interpolated. This includes
most Rust primitive types as well as most of the syntax tree types from [`syn`].

[`quote::ToTokens`]: https://docs.rs/proc-quote/0/proc_quote/trait.ToTokens.html
[`syn`]: https://github.com/dtolnay/syn

```rust
let tokens = quote! {
    struct SerializeWith #generics #where_clause {
        value: &'a #field_ty,
        phantom: core::marker::PhantomData<#item_ty>,
    }

    impl #generics serde::Serialize for SerializeWith #generics #where_clause {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            #path(self.value, serializer)
        }
    }

    SerializeWith {
        value: #value,
        phantom: core::marker::PhantomData::<#item_ty>,
    }
};
```

## Repetition

Repetition is done using `#(...)*` or `#(...),*` similar to `macro_rules!`. This
iterates through the elements of any variable interpolated within the repetition
and inserts a copy of the repetition body for each one. 

- `#(#var)*` — no separators
- `#(#var),*` — the character before the asterisk is used as a separator
- `#( struct #var; )*` — the repetition can contain other things
- `#( #k => println!("{}", #v), )*` — even multiple interpolations
- `#(let #var = self.#var;)*` - the same variable can be used more than once

Note that there is a difference between `#(#var ,)*` and `#(#var),*`—the latter
does not produce a trailing comma. This matches the behavior of delimiters in
`macro_rules!`.

The [`proc_quote::Repeat`](https://docs.rs/proc-quote/0/proc_quote/trait.Repeat.html) 
trait defines which types are allowed to be interpolated inside a repition pattern.

Which types *do* `Repeat`:
  - [`Iterator<T>`] consumes the iterator, iterating through every element.
  - <a href="https://doc.rust-lang.org/std/borrow/trait.Borrow.html">`Borrow<[T]>`</a> 
(includes [`Vec`], [`array`], and [`slice`]) iterates with the [`slice::iter`] method, 
thus not consuming the original data.
  - [`ToTokens`], interpolates the variable in every iteration.

Which types *do NOT* `Repeat`:
  - [`IntoIterator`], to avoid ambiguity (Ex. "Which behavior would have been used for [`Vec`], 
which implements both [`IntoIterator`] and <a href="https://doc.rust-lang.org/std/borrow/trait.Borrow.html">
`Borrow<[T]>`</a>?"; "Which behavior would have been used for [`TokenStream`], which implements both 
[`IntoIterator`] and [`ToTokens`]?"). To use the iterator, you may call [`IntoIterator::into_iter`] 
explicitly.
  - Ambiguous types that implement at least two of the `Repeat` traits. In the very unlikely case 
this happens, disambiguate the type by wrapping it under some structure that only implements the 
trait you desire to use.

[`Iterator<T>`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
[`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
[`array`]: https://doc.rust-lang.org/std/primitive.array.html
[`slice`]: https://doc.rust-lang.org/std/slice/index.html
[`slice::iter`]: https://doc.rust-lang.org/std/primitive.slice.html#method.iter
[`ToTokens`]: https://docs.rs/proc-quote/0/proc_quote/trait.ToTokens.html
[`IntoIterator`]: https://doc.rust-lang.org/std/iter/trait.IntoIterator.html
[`IntoIterator::into_iter`]: https://doc.rust-lang.org/std/iter/trait.IntoIterator.html#tymethod.into_iter

## Returning tokens to the compiler

The `quote!` macro evaluates to an expression of type `proc_macro2::TokenStream`. 
Meanwhile Rust procedural macros are expected to return the type `proc_macro::TokenStream`.

The difference between the two types is that `proc_macro` types are entirely
specific to procedural macros and cannot ever exist in code outside of a
procedural macro, while `proc_macro2` types may exist anywhere including tests
and non-macro code like main.rs and build.rs. This is why even the procedural
macro ecosystem is largely built around `proc_macro2`, because that ensures the
libraries are unit testable and accessible in non-macro contexts.

There is a [`From`]-conversion in both directions so returning the output of
`quote!` from a procedural macro usually looks like `tokens.into()` or
`proc_macro::TokenStream::from(tokens)`.

[`From`]: https://doc.rust-lang.org/std/convert/trait.From.html

## Examples

### Combining quoted fragments

Usually you don't end up constructing an entire final `TokenStream` in one
piece. Different parts may come from different helper functions. The tokens
produced by `quote!` themselves implement `ToTokens` and so can be interpolated
into later `quote!` invocations to build up a final result.

```rust
let type_definition = quote! {...};
let methods = quote! {...};

let tokens = quote! {
    #type_definition
    #methods
};
```

### Constructing identifiers

Suppose we have an identifier `ident` which came from somewhere in a macro
input and we need to modify it in some way for the macro output. Let's consider
prepending the identifier with an underscore.

Simply interpolating the identifier next to an underscore will not have the
behavior of concatenating them. The underscore and the identifier will continue
to be two separate tokens as if you had written `_ x`.

```rust
// incorrect
quote! {
    let mut _#ident = 0;
}
```

The solution is to perform token-level manipulations using the APIs provided by
Syn and proc-macro2.

```rust
let concatenated = format!("_{}", ident);
let varname = syn::Ident::new(&concatenated, ident.span());
quote! {
    let mut #varname = 0;
}
```

### Making method calls

Let's say our macro requires some type specified in the macro input to have a
constructor called `new`. We have the type in a variable called `field_type` of
type `syn::Type` and want to invoke the constructor.

```rust
// incorrect
quote! {
    let value = #field_type::new();
}
```

This works only sometimes. If `field_type` is `String`, the expanded code
contains `String::new()` which is fine. But if `field_type` is something like
`Vec<i32>` then the expanded code is `Vec<i32>::new()` which is invalid syntax.
Ordinarily in handwritten Rust we would write `Vec::<i32>::new()` but for macros
often the following is more convenient.

```rust
quote! {
    let value = <#field_type>::new();
}
```

This expands to `<Vec<i32>>::new()` which behaves correctly.

A similar pattern is appropriate for trait methods.

```rust
quote! {
    let value = <#field_type as core::default::Default>::default();
}
```

## Hygiene

Any interpolated tokens preserve the `Span` information provided by their
`ToTokens` implementation. Tokens that originate within a `quote!` invocation
are spanned with [`Span::call_site()`].

[`Span::call_site()`]: https://docs.rs/proc-macro2/0/proc_macro2/struct.Span.html#method.call_site

A different span can be provided explicitly through the [`quote_spanned!`]
macro.

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
