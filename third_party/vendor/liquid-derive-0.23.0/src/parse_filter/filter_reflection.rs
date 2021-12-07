use super::*;

/// Generates implementation of `FilterReflection`.
fn generate_reflection(filter_parser: &ParseFilter<'_>) -> Result<TokenStream> {
    let ParseFilterMeta {
        filter_name,
        filter_description,
        parameters_struct_name,
        ..
    } = &filter_parser.meta;

    let filter_name = filter_name.as_ref().map_err(|err| err.clone())?;
    let filter_description = filter_description.as_ref().map_err(|err| err.clone())?;

    let impl_filter_reflection =
        filter_parser.generate_impl(quote! { ::liquid_core::parser::FilterReflection });

    let (positional_parameters, keyword_parameters) = if let Some(parameters_struct_name) =
        parameters_struct_name
    {
        (
            quote_spanned! {parameters_struct_name.span()=> <#parameters_struct_name as ::liquid_core::parser::FilterParametersReflection>::positional_parameters() },
            quote_spanned! {parameters_struct_name.span()=> <#parameters_struct_name as ::liquid_core::parser::FilterParametersReflection>::keyword_parameters() },
        )
    } else {
        (quote! { &[] }, quote! { &[] })
    };

    Ok(quote! {
        #impl_filter_reflection {
            fn name(&self) -> &'static str {
                #filter_name
            }
            fn description(&self) -> &'static str {
                #filter_description
            }

            fn positional_parameters(&self) -> &'static [::liquid_core::parser::ParameterReflection] {
                #positional_parameters
            }

            fn keyword_parameters(&self) -> &'static [::liquid_core::parser::ParameterReflection] {
                #keyword_parameters
            }
        }
    })
}

pub fn derive(input: &DeriveInput) -> TokenStream {
    let filter_parser = match ParseFilter::from_input(input) {
        Ok(filter_parser) => filter_parser,
        Err(err) => return err.to_compile_error(),
    };

    match generate_reflection(&filter_parser) {
        Ok(output) => output,
        Err(err) => err.to_compile_error(),
    }
}
