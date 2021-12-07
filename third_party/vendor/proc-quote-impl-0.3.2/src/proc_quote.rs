use proc_macro2::*;
use quote::{quote, quote_spanned, TokenStreamExt};
use std::collections::BTreeSet;

/// Error struct for this crate. This error can be raised
/// into a `TokenStream` that calls `compile_error!` with
/// the given message, at the given span.
struct Error {
    span_s: Span,
    span_e: Option<Span>,
    msg: &'static str,
}

impl Error {
    /// Creates a new Error at the given span with the given
    /// message.
    fn new(span: Span, msg: &'static str) -> Self {
        Self {
            span_s: span,
            span_e: None,
            msg,
        }
    }

    /// Sets the end of the span of this error. The start of
    /// the span is set in `Error::new`.
    fn end_span(mut self, span: Span) -> Self {
        self.span_e = Some(span);
        self
    }

    /// Raises into a `TokenStream` that calls `compile_error!`
    /// with the given message, at the given span.
    fn raise(self) -> TokenStream {
        let Error {
            span_s,
            span_e,
            msg,
        } = self;

        let compile_error = quote_spanned! { span_s=>
            compile_error!(#msg)
        };

        quote_spanned! { span_e.unwrap_or(span_s)=>
            #compile_error ;
        }
    }
}

/// Type alias for results in this crate.
type Result<T> = std::result::Result<T, Error>;

/// Wraps the inner content inside a block with boilerplate to create and return `__stream`.
/// If `requested_span` is some, an aditional `let __span = ...;` line is added before `inner`.
fn generate_quote_header(inner: TokenStream, requested_span: Option<TokenStream>) -> TokenStream {
    let requested_span = if let Some(requested_span) = requested_span {
        quote! { let __span = #requested_span; }
    } else {
        TokenStream::new()
    };

    quote! {
        {
            let mut __stream = ::proc_quote::__rt::TokenStream::new();
            #requested_span
            #inner
            __stream
        }
    }
}

/// Transforms an `Ident` into code that appends the given `Ident` into `__stream`.
fn parse_ident(stream: &mut TokenStream, ident: &Ident) {
    let ref_mut_stream = quote! { &mut __stream };
    let requested_span = quote! { __span };

    let span = ident.span();
    let ident = ident.to_string();
    stream.append_all(quote_spanned! { span=>
        ::proc_quote::__rt::append_ident(#ref_mut_stream, #ident, #requested_span);
    });
}

/// Transforms a `Punct` into code that appends the given `Punct` into `__stream`.
fn parse_punct(stream: &mut TokenStream, punct: &Punct) {
    let ref_mut_stream = quote! { &mut __stream };
    let requested_span = quote! { __span };

    let span = punct.span();
    let spacing = punct.spacing();
    let punct = punct.as_char();
    let append = match spacing {
        Spacing::Alone => quote_spanned! { span=>
            ::proc_quote::__rt::append_punct(#ref_mut_stream, #punct, ::proc_quote::__rt::Spacing::Alone, #requested_span);
        },
        Spacing::Joint => quote_spanned! { span=>
            ::proc_quote::__rt::append_punct(#ref_mut_stream, #punct, ::proc_quote::__rt::Spacing::Joint, #requested_span);
        },
    };
    stream.append_all(append);
}

/// Transforms a `Literal` into code that appends the given `Literal` into `__stream`.
fn parse_literal(stream: &mut TokenStream, lit: &Literal) {
    let ref_mut_stream = quote! { &mut __stream };
    let requested_span = quote! { __span };

    let span = lit.span();
    let lit_to_string = lit.to_string();

    stream.append_all(quote_spanned!{ span=>
        ::proc_quote::__rt::append_stringified_tokens(#ref_mut_stream, #lit_to_string, #requested_span);
    });
}

/// Logic common to `parse_group` and `parse_group_in_iterator_pattern`.
fn parse_group_base(
    stream: &mut TokenStream,
    inner: TokenStream,
    delimiter: Delimiter,
    group_span: Span,
) {
    let ref_mut_stream = quote! { &mut __stream };
    let requested_span = quote! { __span };

    let delimiter = match delimiter {
        Delimiter::Parenthesis => quote! {
            ::proc_quote::__rt::Delimiter::Parenthesis
        },
        Delimiter::Brace => quote! {
            ::proc_quote::__rt::Delimiter::Brace
        },
        Delimiter::Bracket => quote! {
            ::proc_quote::__rt::Delimiter::Bracket
        },
        Delimiter::None => quote! {
            ::proc_quote::__rt::Delimiter::None
        },
    };

    stream.append_all(quote_spanned! { group_span =>
        ::proc_quote::__rt::append_group(#ref_mut_stream, #inner, #delimiter, #requested_span);
    });
}

/// Transforms a `Group` into code that appends the given `Group` into `__stream`.
///
/// Inside iterator patterns, use `parse_group_in_iterator_pattern`.
fn parse_group(stream: &mut TokenStream, group: &Group) -> Result<()> {
    let mut inner = group.stream().into_iter().peekable();
    let inner = parse_token_stream(&mut inner)?;
    let inner = generate_quote_header(inner, None);

    Ok(parse_group_base(
        stream,
        inner,
        group.delimiter(),
        group.span(),
    ))
}

/// Transforms a `Group` into code that appends the given `Group` into `__stream`.
///
/// This function is used inside the iterator patterns, to check for iterators used
/// inside.
fn parse_group_in_iterator_pattern(
    stream: &mut TokenStream,
    group: &Group,
    iter_idents: &mut BTreeSet<Ident>,
) -> Result<()> {
    let mut inner = group.stream().into_iter().peekable();
    let inner = parse_token_stream_in_iterator_pattern(&mut inner, iter_idents)?;
    let inner = generate_quote_header(inner, None);

    Ok(parse_group_base(
        stream,
        inner,
        group.delimiter(),
        group.span(),
    ))
}

/// Helper enum for `interpolation_pattern_type`'s return type.
enum InterpolationPattern {
    /// #ident
    Ident(Ident),

    /// #( group ) token_stream *
    Iterator(Group, TokenStream),

    /// Not an interpolation pattern
    None,
}

/// Alias for common iterator passed to the parsing functions.
type InputIter = std::iter::Peekable<token_stream::IntoIter>;

/// Returns the interpolation pattern type based on the content of the given
/// `punct` and the rest of the `input`.
///
/// Input that is part of the pattern is automatically consumed.
fn interpolation_pattern_type(
    punct: &Punct,
    input: &mut InputIter,
) -> Result<InterpolationPattern> {
    match (punct.as_char(), input.peek()) {
        // #ident
        ('#', Some(TokenTree::Ident(_))) => {
            if let Some(TokenTree::Ident(ident)) = input.next() {
                Ok(InterpolationPattern::Ident(ident))
            } else {
                panic!("guaranteed by previous match")
            }
        }

        // #(group)
        ('#', Some(TokenTree::Group(group))) if group.delimiter() == Delimiter::Parenthesis => {
            let inner = match input.next() {
                Some(TokenTree::Group(inner)) => inner,
                _ => panic!("guaranteed by previous match"),
            };

            let separator = parse_separator(input, inner.span())?;

            Ok(InterpolationPattern::Iterator(inner, separator))
        }

        // Not an interpolation pattern
        _ => Ok(InterpolationPattern::None),
    }
}

/// Interpolates the given variable, which should implement `ToTokens`.
fn interpolate_to_tokens_ident(stream: &mut TokenStream, ident: &Ident) {
    let ref_mut_stream = quote! { &mut __stream };
    let span = ident.span();
    stream.append_all(quote_spanned! { span=>
        ::proc_quote::__rt::append_to_tokens(#ref_mut_stream, & #ident);
    });
}

/// Interpolates the expression inside the group, which should evaluate to
/// something that implements `ToTokens`.
///
/// Returns the vector of idents that were called inside the iterator.
fn interpolate_iterator_group(
    stream: &mut TokenStream,
    group: &Group,
    separator: &TokenStream,
) -> Result<BTreeSet<Ident>> {
    let mut iter_idents = BTreeSet::new();

    let mut inner = group.stream().into_iter().peekable();
    let output = parse_token_stream_in_iterator_pattern(&mut inner, &mut iter_idents)?;

    let mut idents = iter_idents.iter();
    let first = match idents.next() {
        Some(first) => first,
        None => {
            return Err(Error::new(
                group.span(),
                "Expected at least one iterator inside pattern.",
            ));
        }
    };
    let first = quote! { #first };
    let idents_in_tuple = idents.fold(first, |previous, next| quote! { (#previous, #next) });

    let mut idents = iter_idents.iter();
    let first = match idents.next() {
        Some(first) => first,
        None => {
            return Err(Error::new(
                group.span(),
                "Expected at least one iterator inside pattern.",
            ));
        }
    };
    let first_into_iter = quote_spanned!(first.span()=> #first .__proc_quote__as_repeat() );
    let zip_iterators = idents
        .map(|ident| quote_spanned! { ident.span()=> .zip( #ident .__proc_quote__as_repeat() ) });
    if separator.is_empty() {
        stream.append_all(quote! {
            {
                use ::proc_quote::Repeat;
                for #idents_in_tuple in #first_into_iter #(#zip_iterators)* {
                    #output
                }
            }
        });
    } else {
        stream.append_all(quote! {
            {
                use ::proc_quote::Repeat;
                for (__i, #idents_in_tuple) in #first_into_iter #(#zip_iterators)* .enumerate() {
                    if __i > 0 {
                        #separator
                    }
                    #output
                }
            }
        });
    }

    Ok(iter_idents)
}

/// Returns true if the next tokens are jointed '=>', the pattern that separates
/// the span from the template in `quote_spanned!` macro.
fn is_end_span(token: &TokenTree, input: &mut InputIter) -> bool {
    match token {
        TokenTree::Punct(punct) => {
            if punct.as_char() == '=' && punct.spacing() == Spacing::Joint {
                match input.peek() {
                    Some(TokenTree::Punct(punct)) => {
                        punct.as_char() == '>' && punct.spacing() == Spacing::Alone
                    }
                    _ => false,
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Parses the input according to `quote!` rules.
fn parse_token_stream(input: &mut InputIter) -> Result<TokenStream> {
    let mut output = TokenStream::new();

    while let Some(token) = input.next() {
        match &token {
            TokenTree::Group(group) => parse_group(&mut output, group)?,
            TokenTree::Ident(ident) => parse_ident(&mut output, ident),
            TokenTree::Literal(lit) => parse_literal(&mut output, lit),
            TokenTree::Punct(punct) => match interpolation_pattern_type(&punct, input)? {
                InterpolationPattern::Ident(ident) => {
                    interpolate_to_tokens_ident(&mut output, &ident);
                }
                InterpolationPattern::Iterator(group, separator) => {
                    interpolate_iterator_group(&mut output, &group, &separator)?;
                }
                InterpolationPattern::None => {
                    parse_punct(&mut output, punct);
                }
            },
        }
    }

    Ok(output)
}

/// Parses the input according to `quote!` rules inside an iterator pattern.
fn parse_token_stream_in_iterator_pattern(
    input: &mut InputIter,
    iter_idents: &mut BTreeSet<Ident>,
) -> Result<TokenStream> {
    let mut output = TokenStream::new();

    while let Some(token) = input.next() {
        match &token {
            TokenTree::Group(group) => {
                parse_group_in_iterator_pattern(&mut output, group, iter_idents)?
            }
            TokenTree::Ident(ident) => parse_ident(&mut output, ident),
            TokenTree::Literal(lit) => parse_literal(&mut output, lit),
            TokenTree::Punct(punct) => match interpolation_pattern_type(&punct, input)? {
                InterpolationPattern::Ident(ident) => {
                    interpolate_to_tokens_ident(&mut output, &ident);
                    iter_idents.insert(ident);
                }
                InterpolationPattern::Iterator(group, separator) => {
                    iter_idents.append(&mut interpolate_iterator_group(
                        &mut output,
                        &group,
                        &separator,
                    )?);
                }
                InterpolationPattern::None => {
                    parse_punct(&mut output, punct);
                }
            },
        }
    }

    Ok(output)
}

/// Parses the input according to `quote!` rules in an iterator pattern, between
/// the parenthesis and the asterisk.
fn parse_separator(input: &mut InputIter, iterators_span: Span) -> Result<TokenStream> {
    let mut output = TokenStream::new();

    while let Some(token) = input.next() {
        match &token {
            TokenTree::Group(group) => parse_group(&mut output, group)?,
            TokenTree::Ident(ident) => parse_ident(&mut output, ident),
            TokenTree::Literal(lit) => parse_literal(&mut output, lit),
            TokenTree::Punct(punct) => {
                if punct.as_char() == '*' {
                    // The asterisk marks the end of the iterator pattern
                    return Ok(output);
                } else {
                    match interpolation_pattern_type(&punct, input)? {
                        InterpolationPattern::Ident(ident) => {
                            // TODO(#1) don't allow iterator variables
                            interpolate_to_tokens_ident(&mut output, &ident)
                        }
                        InterpolationPattern::Iterator(group, separator) => {
                            let span_s = group.span();
                            let span_e = separator
                                .into_iter()
                                .last()
                                .map(|s| s.span())
                                .unwrap_or(span_s);
                            return Err(Error::new(
                                span_s,
                                "Iterator patterns not supported inside separators.",
                            )
                            .end_span(span_e));
                        }
                        InterpolationPattern::None => {
                            parse_punct(&mut output, punct);
                        }
                    }
                }
            }
        }
    }

    Err(Error::new(
        iterators_span,
        "Iterating interpolation does not have `*` symbol.",
    ))
}

/// Parses the span given in `quote_spanned!`, before '=>'.
fn parse_span(input: &mut InputIter) -> Result<TokenStream> {
    let mut output = TokenStream::new();

    let span_s = input.peek().map(|token| token.span());

    while let Some(token) = input.next() {
        if is_end_span(&token, input) {
            let span_e = input.next().expect("guaranteed by if").span();
            let span_s = span_s.expect("guaranteed inside while");
            if output.is_empty() {
                return Err(Error::new(
                    span_s,
                    "No span given before `=>`. Expected `quote_spanned!{ span=> ... }`.",
                )
                .end_span(span_e));
            } else {
                return Ok(output);
            }
        } else {
            output.append(token);
        }
    }

    Err(Error::new(
        Span::call_site(),
        "Could not find `=>`. Expected `quote_spanned!{ span=> ... }`.",
    ))
}

pub fn quote(input: TokenStream) -> TokenStream {
    let mut input = input.into_iter().peekable();
    let span = quote! { ::proc_quote::__rt::Span::call_site() };
    match parse_token_stream(&mut input) {
        Ok(output) => generate_quote_header(output, Some(span)),
        Err(err) => return err.raise(),
    }
}

pub fn quote_spanned(input: TokenStream) -> TokenStream {
    let mut input = input.into_iter().peekable();
    let span = match parse_span(&mut input) {
        Ok(span) => span,
        Err(err) => return err.raise(),
    };
    match parse_token_stream(&mut input) {
        Ok(output) => generate_quote_header(output, Some(span)),
        Err(err) => return err.raise(),
    }
}
