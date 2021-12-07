use proc_macro2::*;
use proc_quote::*;
use syn::*;

pub fn derive(input: &DeriveInput) -> TokenStream {
    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = input;

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let fields = match get_fields(data) {
        Ok(fields) => fields,
        Err(err) => return err.to_compile_error(),
    };
    let num_fields = fields.len();

    quote! {
        impl #impl_generics ::liquid::ObjectView for #ident #ty_generics #where_clause {
            fn as_value(&self) -> &dyn ::liquid::ValueView {
                self
            }

            fn size(&self) -> i64 {
                #num_fields as i64
            }

            fn keys<'liquid_derive_k>(&'liquid_derive_k self) -> Box<dyn Iterator<Item = ::kstring::KStringCow<'liquid_derive_k>> + 'liquid_derive_k> {
                let mut keys = Vec::with_capacity(#num_fields);
                #(
                    keys.push(::kstring::KStringCow::from_static(stringify!(#fields)));
                )*
                Box::new(keys.into_iter())
            }

            fn values<'liquid_derive_k>(&'liquid_derive_k self) -> Box<dyn Iterator<Item = &'liquid_derive_k dyn ::liquid::ValueView> + 'liquid_derive_k> {
                let mut values = Vec::<&dyn ::liquid::ValueView>::with_capacity(#num_fields);
                #(
                    values.push(&self.#fields);
                )*
                Box::new(values.into_iter())
            }

            fn iter<'liquid_derive_k>(&'liquid_derive_k self) -> Box<dyn Iterator<Item = (::kstring::KStringCow<'liquid_derive_k>, &'liquid_derive_k dyn ::liquid::ValueView)> + 'liquid_derive_k> {
                let mut values = Vec::<(::kstring::KStringCow<'liquid_derive_k>, &'liquid_derive_k dyn ::liquid::ValueView)>::with_capacity(#num_fields);
                #(
                    values.push((
                        ::kstring::KStringCow::from_static(stringify!(#fields)),
                        &self.#fields,
                    ));
                )*
                Box::new(values.into_iter())
            }

            fn contains_key(&self, index: &str) -> bool {
                match index {
                    #(
                        stringify!(#fields) => true,
                    )*
                    _ => false,
                }
            }

            fn get<'liquid_derive_s>(&'liquid_derive_s self, index: &str) -> Option<&'liquid_derive_s dyn ::liquid::ValueView> {
                match index {
                    #(
                        stringify!(#fields) => Some(&self.#fields),
                    )*
                    _ => None,
                }
            }
        }
    }
}

pub fn core_derive(input: &DeriveInput) -> TokenStream {
    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = input;

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let fields = match get_fields(data) {
        Ok(fields) => fields,
        Err(err) => return err.to_compile_error(),
    };
    let num_fields = fields.len();

    quote! {
        impl #impl_generics ::liquid_core::ObjectView for #ident #ty_generics #where_clause {
            fn as_value(&self) -> &dyn ::liquid_core::ValueView {
                self
            }

            fn size(&self) -> i64 {
                #num_fields as i64
            }

            fn keys<'liquid_derive_k>(&'liquid_derive_k self) -> Box<dyn Iterator<Item = ::kstring::KStringCow<'liquid_derive_k>> + 'liquid_derive_k> {
                let mut keys = Vec::with_capacity(#num_fields);
                #(
                    keys.push(::kstring::KStringCow::from_static(stringify!(#fields)));
                )*
                Box::new(keys.into_iter())
            }

            fn values<'liquid_derive_k>(&'liquid_derive_k self) -> Box<dyn Iterator<Item = &'liquid_derive_k dyn ::liquid_core::ValueView> + 'liquid_derive_k> {
                let mut values = Vec::<&dyn ::liquid_core::ValueView>::with_capacity(#num_fields);
                #(
                    values.push(&self.#fields);
                )*
                Box::new(values.into_iter())
            }

            fn iter<'liquid_derive_k>(&'liquid_derive_k self) -> Box<dyn Iterator<Item = (::kstring::KStringCow<'liquid_derive_k>, &'liquid_derive_k dyn ::liquid_core::ValueView)> + 'liquid_derive_k> {
                let mut values = Vec::<(::kstring::KStringCow<'liquid_derive_k>, &'liquid_derive_k dyn ::liquid_core::ValueView)>::with_capacity(#num_fields);
                #(
                    values.push((
                        ::kstring::KStringCow::from_static(stringify!(#fields)),
                        &self.#fields,
                    ));
                )*
                Box::new(values.into_iter())
            }

            fn contains_key(&self, index: &str) -> bool {
                match index {
                    #(
                        stringify!(#fields) => true,
                    )*
                    _ => false,
                }
            }

            fn get<'liquid_derive_s>(&'liquid_derive_s self, index: &str) -> Option<&'liquid_derive_s dyn ::liquid_core::ValueView> {
                match index {
                    #(
                        stringify!(#fields) => Some(&self.#fields),
                    )*
                    _ => None,
                }
            }
        }
    }
}

pub(crate) fn get_fields(data: &Data) -> Result<Vec<&Ident>> {
    let fields = match data {
        Data::Struct(data) => &data.fields,
        Data::Enum(data) => {
            return Err(Error::new_spanned(
                data.enum_token,
                "`ObjectView` support for `enum` is unimplemented.",
            ));
        }
        Data::Union(data) => {
            return Err(Error::new_spanned(
                data.union_token,
                "Unions cannot impl ObjectView.",
            ));
        }
    };

    let fields = match fields {
        Fields::Named(fields) => fields,
        Fields::Unnamed(fields) => {
            return Err(Error::new_spanned(
                fields,
                "`ObjectView` support for tuple-structs is unimplemented.",
            ))
        }
        Fields::Unit => {
            return Err(Error::new_spanned(
                fields,
                "`ObjectView` support for unit-structs is unimplemented.",
            ))
        }
    };

    Ok(fields
        .named
        .iter()
        .map(|field| field.ident.as_ref().expect("Fields are named."))
        .collect())
}
