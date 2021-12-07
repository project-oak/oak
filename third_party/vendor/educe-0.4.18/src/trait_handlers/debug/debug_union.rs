use super::super::TraitHandler;
use super::models::{
    FieldAttributeBuilder, FieldAttributeName, TypeAttributeBuilder, TypeAttributeName,
};

use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Generics, Meta};
use crate::Trait;

pub struct DebugUnionHandler;

impl TraitHandler for DebugUnionHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        let type_attribute = TypeAttributeBuilder {
            enable_flag: true,
            name: TypeAttributeName::Default,
            enable_name: true,
            named_field: false,
            enable_named_field: false,
            enable_bound: true,
        }
        .from_debug_meta(meta);

        let name = type_attribute.name.into_string_by_ident(&ast.ident);

        let bound = type_attribute
            .bound
            .into_punctuated_where_predicates_by_generic_parameters(&ast.generics.params);

        let mut builder_tokens = TokenStream::new();

        if let Data::Union(data) = &ast.data {
            for field in data.fields.named.iter() {
                let _ = FieldAttributeBuilder {
                    name: FieldAttributeName::Default,
                    enable_name: false,
                    enable_ignore: false,
                    enable_impl: false,
                }
                .from_attributes(&field.attrs, traits);
            }

            if name.is_empty() {
                builder_tokens.extend(quote!(
                    let size = core::mem::size_of::<Self>();
                    let data = unsafe {{ core::slice::from_raw_parts(self as *const Self as *const u8, size) }};

                    core::fmt::Debug::fmt(data, formatter)
                ));
            } else {
                builder_tokens.extend(quote!(
                    let mut builder = formatter.debug_tuple(#name);

                    let size = core::mem::size_of::<Self>();

                    let data = unsafe {{ core::slice::from_raw_parts(self as *const Self as *const u8, size) }};

                    builder.field(&data);

                    builder.finish()
                ));
            }
        }

        let ident = &ast.ident;

        let mut generics_cloned: Generics = ast.generics.clone();

        let where_clause = generics_cloned.make_where_clause();

        where_clause.predicates.extend(bound.iter().cloned());

        let (impl_generics, ty_generics, where_clause) = generics_cloned.split_for_impl();

        let debug_impl = quote! {
            impl #impl_generics core::fmt::Debug for #ident #ty_generics #where_clause {
                #[inline]
                fn fmt(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    #builder_tokens
                }
            }
        };

        tokens.extend(debug_impl);
    }
}
