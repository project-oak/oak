//! This crate provides the [`quote!`] macro for turning Rust syntax tree data
//! structures into tokens of source code.
//!
//! [`quote!`]: macro.quote.html
//!
//! Procedural macros in Rust receive a stream of tokens as input, execute
//! arbitrary Rust code to determine how to manipulate those tokens, and produce
//! a stream of tokens to hand back to the compiler to compile into the caller's
//! crate. Quasi-quoting is a solution to one piece of that -- producing tokens
//! to return to the compiler.
//!
//! The idea of quasi-quoting is that we write *code* that we treat as *data*.
//! Within the `quote!` macro, we can write what looks like code to our text
//! editor or IDE. We get all the benefits of the editor's brace matching,
//! syntax highlighting, indentation, and maybe autocompletion. But rather than
//! compiling that as code into the current crate, we can treat it as data, pass
//! it around, mutate it, and eventually hand it back to the compiler as tokens
//! to compile into the macro caller's crate.
//!
//! This crate is motivated by the procedural macro use case, but it is a
//! general-purpose Rust quasi-quoting library and is not specific to procedural
//! macros.
//!
//! # Example
//!
//! The following quasi-quoted block of code is something you might find in [a]
//! procedural macro having to do with data structure serialization. The `#var`
//! syntax performs interpolation of runtime variables into the quoted tokens.
//! Check out the documentation of the [`quote!`] macro for more detail about
//! the syntax. See also the [`quote_spanned!`] macro which is important for
//! implementing hygienic procedural macros.
//!
//! [a]: https://serde.rs/
//! [`quote_spanned!`]: macro.quote_spanned.html
//!
//! ```edition2018
//! # use quote::quote;
//! #
//! # let generics = "";
//! # let where_clause = "";
//! # let field_ty = "";
//! # let item_ty = "";
//! # let path = "";
//! # let value = "";
//! #
//! let tokens = quote! {
//!     struct SerializeWith #generics #where_clause {
//!         value: &'a #field_ty,
//!         phantom: core::marker::PhantomData<#item_ty>,
//!     }
//!
//!     impl #generics serde::Serialize for SerializeWith #generics #where_clause {
//!         fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//!         where
//!             S: serde::Serializer,
//!         {
//!             #path(self.value, serializer)
//!         }
//!     }
//!
//!     SerializeWith {
//!         value: #value,
//!         phantom: core::marker::PhantomData::<#item_ty>,
//!     }
//! };
//! ```
use proc_macro_hack::proc_macro_hack;

mod repeat;

pub use self::repeat::*;
pub use quote::ToTokens;
pub use quote::TokenStreamExt;

/// The whole point.
///
/// Performs variable interpolation against the input and produces it as
/// [`TokenStream`]. For returning tokens to the compiler in a procedural macro, use
/// `into()` to build a `TokenStream`.
///
/// [`TokenStream`]: https://docs.rs/proc-macro2/0/proc_macro2/struct.TokenStream.html
///
/// # Interpolation
///
/// Variable interpolation is done with `#var` (similar to `$var` in
/// `macro_rules!` macros). This grabs the `var` variable that is currently in
/// scope and inserts it in that location in the output tokens. Any type
/// implementing the [`ToTokens`] trait can be interpolated. This includes most
/// Rust primitive types as well as most of the syntax tree types from the [Syn]
/// crate.
///
/// [`ToTokens`]: trait.ToTokens.html
/// [Syn]: https://github.com/dtolnay/syn
///
/// Repetition is done using `#(...)*` or `#(...),*` again similar to
/// `macro_rules!`. This iterates through the elements of any variable
/// interpolated within the repetition and inserts a copy of the repetition
/// body for each one.
///
/// - `#(#var)*` — no separators
/// - `#(#var),*` — the character before the asterisk is used as a separator
/// - `#( struct #var; )*` — the repetition can contain other tokens
/// - `#( #k => println!("{}", #v), )*` — even multiple interpolations
/// - `#(let #var = self.#var;)*` - the same variable can be used more than once
///
/// The [`proc_quote::Repeat`](https://docs.rs/proc-quote/0/proc_quote/trait.Repeat.html)
/// trait defines which types are allowed to be interpolated inside a repition pattern.
///
/// Which types that implement the following traits *do* `Repeat`:
///   - [`Iterator<T>`] consumes the iterator, iterating through every element.
///   - <a href="https://doc.rust-lang.org/std/borrow/trait.Borrow.html">`Borrow<[T]>`</a>
/// (includes [`Vec`], [`array`], and [`slice`]) iterates with the [`slice::iter`] method,
/// thus not consuming the original data.
///   - [`ToTokens`], interpolates the variable in every iteration.
///
/// Which types *do NOT* `Repeat`:
///   - [`IntoIterator`], to avoid ambiguity (Ex. "Which behavior would have been used for [`Vec`],
/// which implements both [`IntoIterator`] and <a href="https://doc.rust-lang.org/std/borrow/trait.Borrow.html">
/// `Borrow<[T]>`</a>?"; "Which behavior would have been used for [`TokenStream`], which implements both
/// [`IntoIterator`] and [`ToTokens`]?"). To use the iterator, you may call [`IntoIterator::into_iter`]
/// explicitly.
///   - Ambiguous types that implement at least two of the `Repeat` traits. In the very unlikely case
/// this happens, disambiguate the type by wrapping it under some structure that only implements the
/// trait you desire to use.
///
/// [`Iterator<T>`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
/// [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
/// [`array`]: https://doc.rust-lang.org/std/primitive.array.html
/// [`slice`]: https://doc.rust-lang.org/std/slice/index.html
/// [`slice::iter`]: https://doc.rust-lang.org/std/primitive.slice.html#method.iter
/// [`ToTokens`]: https://docs.rs/proc-quote/0/proc_quote/trait.ToTokens.html
/// [`IntoIterator`]: https://doc.rust-lang.org/std/iter/trait.IntoIterator.html
/// [`IntoIterator::into_iter`]: https://doc.rust-lang.org/std/iter/trait.IntoIterator.html#tymethod.into_iter
///
/// # Hygiene
///
/// Any interpolated tokens preserve the `Span` information provided by their
/// `ToTokens` implementation. Tokens that originate within the `quote!`
/// invocation are spanned with [`Span::call_site()`].
///
/// [`Span::call_site()`]: https://docs.rs/proc-macro2/0/proc_macro2/struct.Span.html#method.call_site
///
/// A different span can be provided through the [`quote_spanned!`] macro.
///
/// [`quote_spanned!`]: macro.quote_spanned.html
///
/// # Return type
///
/// The macro evaluates to an expression of type `proc_macro2::TokenStream`.
/// Meanwhile Rust procedural macros are expected to return the type
/// `proc_macro::TokenStream`.
///
/// The difference between the two types is that `proc_macro` types are entirely
/// specific to procedural macros and cannot ever exist in code outside of a
/// procedural macro, while `proc_macro2` types may exist anywhere including
/// tests and non-macro code like main.rs and build.rs. This is why even the
/// procedural macro ecosystem is largely built around `proc_macro2`, because
/// that ensures the libraries are unit testable and accessible in non-macro
/// contexts.
///
/// There is a [`From`]-conversion in both directions so returning the output of
/// `quote!` from a procedural macro usually looks like `tokens.into()` or
/// `proc_macro::TokenStream::from(tokens)`.
///
/// [`From`]: https://doc.rust-lang.org/std/convert/trait.From.html
///
/// # Examples
///
/// ## Procedural macro
///
/// The structure of a basic procedural macro is as follows. Refer to the [Syn]
/// crate for further useful guidance on using `quote!` as part of a procedural
/// macro.
///
/// [Syn]: https://github.com/dtolnay/syn
///
/// ```edition2018
/// # #[cfg(any())]
/// extern crate proc_macro;
/// # use proc_macro2 as proc_macro;
///
/// use proc_macro::TokenStream;
/// use quote::quote;
///
/// # const IGNORE_TOKENS: &'static str = stringify! {
/// #[proc_macro_derive(HeapSize)]
/// # };
/// pub fn derive_heap_size(input: TokenStream) -> TokenStream {
///     // Parse the input and figure out what implementation to generate...
///     # const IGNORE_TOKENS: &'static str = stringify! {
///     let name = /* ... */;
///     let expr = /* ... */;
///     # };
///     #
///     # let name = 0;
///     # let expr = 0;
///
///     let expanded = quote! {
///         // The generated impl.
///         impl heapsize::HeapSize for #name {
///             fn heap_size_of_children(&self) -> usize {
///                 #expr
///             }
///         }
///     };
///
///     // Hand the output tokens back to the compiler.
///     TokenStream::from(expanded)
/// }
/// ```
///
/// ## Combining quoted fragments
///
/// Usually you don't end up constructing an entire final `TokenStream` in one
/// piece. Different parts may come from different helper functions. The tokens
/// produced by `quote!` themselves implement `ToTokens` and so can be
/// interpolated into later `quote!` invocations to build up a final result.
///
/// ```edition2018
/// # use quote::quote;
/// #
/// let type_definition = quote! {...};
/// let methods = quote! {...};
///
/// let tokens = quote! {
///     #type_definition
///     #methods
/// };
/// ```
///
/// ## Constructing identifiers
///
/// Suppose we have an identifier `ident` which came from somewhere in a macro
/// input and we need to modify it in some way for the macro output. Let's
/// consider prepending the identifier with an underscore.
///
/// Simply interpolating the identifier next to an underscore will not have the
/// behavior of concatenating them. The underscore and the identifier will
/// continue to be two separate tokens as if you had written `_ x`.
///
/// ```edition2018
/// # use proc_macro2::{self as syn, Span};
/// # use quote::quote;
/// #
/// # let ident = syn::Ident::new("i", Span::call_site());
/// #
/// // incorrect
/// quote! {
///     let mut _#ident = 0;
/// }
/// # ;
/// ```
///
/// The solution is to perform token-level manipulations using the APIs provided
/// by Syn and proc-macro2.
///
/// ```edition2018
/// # use proc_macro2::{self as syn, Span};
/// # use quote::quote;
/// #
/// # let ident = syn::Ident::new("i", Span::call_site());
/// #
/// let concatenated = format!("_{}", ident);
/// let varname = syn::Ident::new(&concatenated, ident.span());
/// quote! {
///     let mut #varname = 0;
/// }
/// # ;
/// ```
///
/// ## Making method calls
///
/// Let's say our macro requires some type specified in the macro input to have
/// a constructor called `new`. We have the type in a variable called
/// `field_type` of type `syn::Type` and want to invoke the constructor.
///
/// ```edition2018
/// # use quote::quote;
/// #
/// # let field_type = quote!(...);
/// #
/// // incorrect
/// quote! {
///     let value = #field_type::new();
/// }
/// # ;
/// ```
///
/// This works only sometimes. If `field_type` is `String`, the expanded code
/// contains `String::new()` which is fine. But if `field_type` is something
/// like `Vec<i32>` then the expanded code is `Vec<i32>::new()` which is invalid
/// syntax. Ordinarily in handwritten Rust we would write `Vec::<i32>::new()`
/// but for macros often the following is more convenient.
///
/// ```edition2018
/// # use quote::quote;
/// #
/// # let field_type = quote!(...);
/// #
/// quote! {
///     let value = <#field_type>::new();
/// }
/// # ;
/// ```
///
/// This expands to `<Vec<i32>>::new()` which behaves correctly.
///
/// A similar pattern is appropriate for trait methods.
///
/// ```edition2018
/// # use quote::quote;
/// #
/// # let field_type = quote!(...);
/// #
/// quote! {
///     let value = <#field_type as core::default::Default>::default();
/// }
/// # ;
/// ```
#[proc_macro_hack]
pub use proc_quote_impl::quote;

/// Same as `quote!`, but applies a given span to all tokens originating within
/// the macro invocation.
///
/// # Syntax
///
/// A span expression of type [`Span`], followed by `=>`, followed by the tokens
/// to quote. The span expression should be brief -- use a variable for anything
/// more than a few characters. There should be no space before the `=>` token.
///
/// [`Span`]: https://docs.rs/proc-macro2/0.4/proc_macro2/struct.Span.html
///
/// ```edition2018
/// # use proc_macro2::Span;
/// # use quote::quote_spanned;
/// #
/// # const IGNORE_TOKENS: &'static str = stringify! {
/// let span = /* ... */;
/// # };
/// # let span = Span::call_site();
/// # let init = 0;
///
/// // On one line, use parentheses.
/// let tokens = quote_spanned!(span=> Box::into_raw(Box::new(#init)));
///
/// // On multiple lines, place the span at the top and use braces.
/// let tokens = quote_spanned! {span=>
///     Box::into_raw(Box::new(#init))
/// };
/// ```
///
/// The lack of space before the `=>` should look jarring to Rust programmers
/// and this is intentional. The formatting is designed to be visibly
/// off-balance and draw the eye a particular way, due to the span expression
/// being evaluated in the context of the procedural macro and the remaining
/// tokens being evaluated in the generated code.
///
/// # Hygiene
///
/// Any interpolated tokens preserve the `Span` information provided by their
/// `ToTokens` implementation. Tokens that originate within the `quote_spanned!`
/// invocation are spanned with the given span argument.
///
/// # Example
///
/// The following procedural macro code uses `quote_spanned!` to assert that a
/// particular Rust type implements the [`Sync`] trait so that references can be
/// safely shared between threads.
///
/// [`Sync`]: https://doc.rust-lang.org/std/marker/trait.Sync.html
///
/// ```edition2018
/// # use quote::{quote_spanned, TokenStreamExt, ToTokens};
/// # use proc_macro2::{Span, TokenStream};
/// #
/// # struct Type;
/// #
/// # impl Type {
/// #     fn span(&self) -> Span {
/// #         Span::call_site()
/// #     }
/// # }
/// #
/// # impl ToTokens for Type {
/// #     fn to_tokens(&self, _tokens: &mut TokenStream) {}
/// # }
/// #
/// # let ty = Type;
/// # let call_site = Span::call_site();
/// #
/// let ty_span = ty.span();
/// let assert_sync = quote_spanned! {ty_span=>
///     struct _AssertSync where #ty: Sync;
/// };
/// ```
///
/// If the assertion fails, the user will see an error like the following. The
/// input span of their type is hightlighted in the error.
///
/// ```text
/// error[E0277]: the trait bound `*const (): std::marker::Sync` is not satisfied
///   --> src/main.rs:10:21
///    |
/// 10 |     static ref PTR: *const () = &();
///    |                     ^^^^^^^^^ `*const ()` cannot be shared between threads safely
/// ```
///
/// In this example it is important for the where-clause to be spanned with the
/// line/column information of the user's input type so that error messages are
/// placed appropriately by the compiler. But it is also incredibly important
/// that `Sync` resolves at the macro definition site and not the macro call
/// site. If we resolve `Sync` at the same span that the user's type is going to
/// be resolved, then they could bypass our check by defining their own trait
/// named `Sync` that is implemented for their type.
#[proc_macro_hack]
pub use proc_quote_impl::quote_spanned;

// Not public API.
#[doc(hidden)]
pub mod __rt {
    use super::*;
    pub use proc_macro2::*;

    pub fn append_ident(stream: &mut TokenStream, ident: &str, span: Span) {
        // TODO(blocked on rust-lang/rust#54723)
        // https://github.com/rust-lang/rust/issues/54723
        // Use `new_raw` once it's stabilized
        // stream.append(Ident::new_raw(ident, span));
        match syn::parse_str::<Ident>(ident) {
            Ok(mut ident) => {
                ident.set_span(span);
                stream.append(ident);
            }
            Err(_) => stream.append(Ident::new(ident, span)),
        }
    }

    pub fn append_punct(stream: &mut TokenStream, punct: char, spacing: Spacing, span: Span) {
        let mut punct = Punct::new(punct, spacing);
        punct.set_span(span);
        stream.append(punct);
    }

    pub fn append_stringified_tokens(stream: &mut TokenStream, s: &str, span: Span) {
        let s: TokenStream = s.parse().expect("invalid token stream");
        stream.extend(s.into_iter().map(|mut t| {
            t.set_span(span);
            t
        }));
    }

    pub fn append_to_tokens<T: ToTokens>(stream: &mut TokenStream, to_tokens: &T) {
        to_tokens.to_tokens(stream);
    }

    pub fn append_group(
        stream: &mut TokenStream,
        inner: TokenStream,
        delimiter: Delimiter,
        span: Span,
    ) {
        let mut group = Group::new(delimiter, inner);
        group.set_span(span);
        stream.append(group);
    }
}
