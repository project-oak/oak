use super::*;

/// Generates implementation of `ParseFilter`.
fn generate_parse_filter(filter_parser: &ParseFilter<'_>) -> Result<TokenStream> {
    let ParseFilterMeta {
        parameters_struct_name,
        filter_struct_name,
        ..
    } = &filter_parser.meta;

    let filter_struct_name = filter_struct_name.as_ref().map_err(|err| err.clone())?;

    let impl_parse_filter =
        filter_parser.generate_impl(quote! { ::liquid_core::parser::ParseFilter });

    if let Some(parameters_struct_name) = parameters_struct_name {
        let build_filter_parameters = quote_spanned! {parameters_struct_name.span()=>
            let args = <#parameters_struct_name as ::liquid_core::parser::FilterParameters>::from_args(args)?;
        };

        let return_expr = quote_spanned! {filter_struct_name.span()=>
            Ok(::std::boxed::Box::new(<#filter_struct_name as ::std::convert::From<#parameters_struct_name>>::from(args)))
        };

        Ok(quote! {
            #impl_parse_filter {
                fn parse(&self, args: ::liquid_core::parser::FilterArguments) -> ::liquid_core::error::Result<::std::boxed::Box<::liquid_core::parser::Filter>> {
                    #build_filter_parameters
                    #return_expr
                }

                fn reflection(&self) -> &::liquid_core::parser::FilterReflection {
                    self
                }
            }
        })
    } else {
        let return_expr = quote_spanned! {filter_struct_name.span()=>
            ::std::result::Result::Ok(::std::boxed::Box::new(<#filter_struct_name as ::std::default::Default>::default()))
        };
        Ok(quote! {
            #impl_parse_filter {
                fn parse(&self, mut args: ::liquid_core::parser::FilterArguments) -> ::liquid_core::error::Result<::std::boxed::Box<::liquid_core::parser::Filter>> {
                    if let ::std::option::Option::Some(arg) = args.positional.next() {
                        return ::std::result::Result::Err(::liquid_core::error::Error::with_msg("Invalid number of positional arguments")
                            .context("cause", concat!("expected at most 0 positional arguments"))
                        );
                    }
                    if let ::std::option::Option::Some(arg) = args.keyword.next() {
                        return ::std::result::Result::Err(::liquid_core::error::Error::with_msg(format!("Unexpected named argument `{}`", arg.0)));
                    }

                    #return_expr
                }

                fn reflection(&self) -> &::liquid_core::parser::FilterReflection {
                    self
                }
            }
        })
    }
}

pub fn derive(input: &DeriveInput) -> TokenStream {
    let filter_parser = match ParseFilter::from_input(input) {
        Ok(filter_parser) => filter_parser,
        Err(err) => return err.to_compile_error(),
    };

    match generate_parse_filter(&filter_parser) {
        Ok(output) => output,
        Err(err) => err.to_compile_error(),
    }
}
