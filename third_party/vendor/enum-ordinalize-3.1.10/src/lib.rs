/*!
# Enum Ordinalize

This crates provides a procedural macro to let enums not only get its variants' ordinal but also be constructed from an ordinal.

## Ordinalize

Use `#[derive(Ordinalize)]` to make an enum (which must only has unit variants) have `from_ordinal_unsafe`, `from_ordinal`, `variants`, and `variant_count` associated functions and a `ordinal` method.

```rust
#[macro_use] extern crate enum_ordinalize;

#[derive(Debug, PartialEq, Eq, Ordinalize)]
enum MyEnum {
    Zero,
    One,
    Two,
}

assert_eq!(0i8, MyEnum::Zero.ordinal());
assert_eq!(1i8, MyEnum::One.ordinal());
assert_eq!(2i8, MyEnum::Two.ordinal());

assert_eq!(Some(MyEnum::Zero), MyEnum::from_ordinal(0i8));
assert_eq!(Some(MyEnum::One), MyEnum::from_ordinal(1i8));
assert_eq!(Some(MyEnum::Two), MyEnum::from_ordinal(2i8));

assert_eq!(MyEnum::Zero, unsafe { MyEnum::from_ordinal_unsafe(0i8) });
assert_eq!(MyEnum::One, unsafe { MyEnum::from_ordinal_unsafe(1i8) });
assert_eq!(MyEnum::Two, unsafe { MyEnum::from_ordinal_unsafe(2i8) });
```

### Get Variants

```rust
#[macro_use] extern crate enum_ordinalize;

#[derive(Debug, PartialEq, Eq, Ordinalize)]
enum MyEnum {
    Zero,
    One,
    Two,
}

assert_eq!([MyEnum::Zero, MyEnum::One, MyEnum::Two], MyEnum::variants());
assert_eq!(3, MyEnum::variant_count());
```

`variants` and `variant_count` are constant functions.

## The (Ordinal) Size of an Enum

The ordinal value is an integer whose size is determined by the enum itself. The larger (or the smaller if it's negative) the variants' values are, the bigger the enum size is.

For example,

```rust
#[macro_use] extern crate enum_ordinalize;

#[derive(Debug, PartialEq, Eq, Ordinalize)]
enum MyEnum {
    Zero,
    One,
    Two,
    Thousand = 1000,
}

assert_eq!(0i16, MyEnum::Zero.ordinal());
assert_eq!(1i16, MyEnum::One.ordinal());
assert_eq!(2i16, MyEnum::Two.ordinal());

assert_eq!(Some(MyEnum::Zero), MyEnum::from_ordinal(0i16));
assert_eq!(Some(MyEnum::One), MyEnum::from_ordinal(1i16));
assert_eq!(Some(MyEnum::Two), MyEnum::from_ordinal(2i16));

assert_eq!(MyEnum::Zero, unsafe { MyEnum::from_ordinal_unsafe(0i16) });
assert_eq!(MyEnum::One, unsafe { MyEnum::from_ordinal_unsafe(1i16) });
assert_eq!(MyEnum::Two, unsafe { MyEnum::from_ordinal_unsafe(2i16) });
```

In order to store `1000`, the size of `MyEnum` grows. Thus, the ordinal is in `i16` instead of `i8`.

You can use the `#[repr(type)]` attribute to control the size explicitly. For instance,

```rust
#[macro_use] extern crate enum_ordinalize;

#[derive(Debug, PartialEq, Eq, Ordinalize)]
#[repr(usize)]
enum MyEnum {
    Zero,
    One,
    Two,
    Thousand = 1000,
}

assert_eq!(0usize, MyEnum::Zero.ordinal());
assert_eq!(1usize, MyEnum::One.ordinal());
assert_eq!(2usize, MyEnum::Two.ordinal());

assert_eq!(Some(MyEnum::Zero), MyEnum::from_ordinal(0usize));
assert_eq!(Some(MyEnum::One), MyEnum::from_ordinal(1usize));
assert_eq!(Some(MyEnum::Two), MyEnum::from_ordinal(2usize));

assert_eq!(MyEnum::Zero, unsafe { MyEnum::from_ordinal_unsafe(0usize) });
assert_eq!(MyEnum::One, unsafe { MyEnum::from_ordinal_unsafe(1usize) });
assert_eq!(MyEnum::Two, unsafe { MyEnum::from_ordinal_unsafe(2usize) });
```

## Useful Increment

The integers represented by variants are extended in successive increments and can be set explicitly from anywhere.

```rust
#[macro_use] extern crate enum_ordinalize;

#[derive(Debug, PartialEq, Eq, Ordinalize)]
enum MyEnum {
    Two   = 2,
    Three,
    Four,
    Eight = 8,
    Nine,
    NegativeTen = -10,
    NegativeNine,
}

assert_eq!(4i8, MyEnum::Four.ordinal());
assert_eq!(9i8, MyEnum::Nine.ordinal());
assert_eq!(-9i8, MyEnum::NegativeNine.ordinal());

assert_eq!(Some(MyEnum::Four), MyEnum::from_ordinal(4i8));
assert_eq!(Some(MyEnum::Nine), MyEnum::from_ordinal(9i8));
assert_eq!(Some(MyEnum::NegativeNine), MyEnum::from_ordinal(-9i8));

assert_eq!(MyEnum::Four, unsafe { MyEnum::from_ordinal_unsafe(4i8) });
assert_eq!(MyEnum::Nine, unsafe { MyEnum::from_ordinal_unsafe(9i8) });
assert_eq!(MyEnum::NegativeNine, unsafe { MyEnum::from_ordinal_unsafe(-9i8) });
```
*/

#![no_std]

extern crate alloc;
extern crate proc_macro;
extern crate syn;

#[macro_use]
extern crate quote;

extern crate num_bigint;

mod big_int_wrapper;
mod panic;
mod variant_type;

use core::str::FromStr;

use alloc::string::ToString;
use alloc::vec::Vec;

use proc_macro::TokenStream;
use quote::ToTokens;
use syn::{Data, DeriveInput, Expr, Fields, Ident, Lit, Meta, NestedMeta, UnOp};

use num_bigint::BigInt;

use big_int_wrapper::BigIntWrapper;
use variant_type::VariantType;

fn derive_input_handler(ast: DeriveInput) -> TokenStream {
    let mut variant_type = VariantType::default();

    for attr in ast.attrs.iter() {
        if let Some(attr_meta_name) = attr.path.get_ident() {
            if attr_meta_name == "repr" {
                // #[repr(u8)], #[repr(u16)], ..., etc.
                let attr_meta = attr.parse_meta().unwrap();

                if let Meta::List(list) = attr_meta {
                    for p in &list.nested {
                        if let NestedMeta::Meta(Meta::Path(path)) = p {
                            let meta_name = path.into_token_stream().to_string();

                            variant_type = VariantType::from_str(meta_name);

                            break;
                        }
                    }
                }
            }
        }
    }

    let name = &ast.ident;

    match ast.data {
        Data::Enum(data) => {
            if data.variants.is_empty() {
                panic::no_variant();
            }

            let mut values: Vec<BigIntWrapper> = Vec::with_capacity(data.variants.len());
            let mut variant_idents: Vec<&Ident> = Vec::with_capacity(data.variants.len());
            let mut use_constant_counter = false;

            if VariantType::Nondetermined == variant_type {
                let mut min = BigInt::from(u128::max_value());
                let mut max = BigInt::from(i128::min_value());
                let mut counter = BigInt::default();

                for variant in data.variants.iter() {
                    if let Fields::Unit = variant.fields {
                        let value = if let Some((_, exp)) = variant.discriminant.as_ref() {
                            match exp {
                                Expr::Lit(lit) => {
                                    let lit = &lit.lit;

                                    let value = match lit {
                                        Lit::Int(value) => {
                                            let value = value.base10_digits();
                                            BigInt::from_str(value).unwrap()
                                        }
                                        _ => panic::unsupported_discriminant(),
                                    };

                                    counter = value.clone();

                                    value
                                }
                                Expr::Unary(unary) => {
                                    match unary.op {
                                        UnOp::Neg(_) => match unary.expr.as_ref() {
                                            Expr::Lit(lit) => {
                                                let lit = &lit.lit;

                                                let value = match lit {
                                                    Lit::Int(value) => {
                                                        let value = value.base10_digits();

                                                        -BigInt::from_str(value).unwrap()
                                                    }
                                                    _ => panic::unsupported_discriminant(),
                                                };

                                                counter = value.clone();

                                                value
                                            }
                                            Expr::Path(_)
                                            | Expr::Cast(_)
                                            | Expr::Binary(_)
                                            | Expr::Call(_) => {
                                                panic::constant_variable_on_non_determined_size_enum(
                                                )
                                            }
                                            _ => panic::unsupported_discriminant(),
                                        },
                                        _ => panic::unsupported_discriminant(),
                                    }
                                }
                                Expr::Path(_) | Expr::Cast(_) | Expr::Binary(_) | Expr::Call(_) => {
                                    panic::constant_variable_on_non_determined_size_enum()
                                }
                                _ => panic::unsupported_discriminant(),
                            }
                        } else {
                            counter.clone()
                        };

                        if min > value {
                            min = value.clone();
                        }

                        if max < value {
                            max = value.clone();
                        }

                        variant_idents.push(&variant.ident);

                        counter += 1;

                        values.push(BigIntWrapper::from(value));
                    } else {
                        panic::not_unit_variant();
                    }
                }

                if min >= BigInt::from(i8::min_value()) && max <= BigInt::from(i8::max_value()) {
                    variant_type = VariantType::I8;
                } else if min >= BigInt::from(i16::min_value())
                    && max <= BigInt::from(i16::max_value())
                {
                    variant_type = VariantType::I16;
                } else if min >= BigInt::from(i32::min_value())
                    && max <= BigInt::from(i32::max_value())
                {
                    variant_type = VariantType::I32;
                } else if min >= BigInt::from(i64::min_value())
                    && max <= BigInt::from(i64::max_value())
                {
                    variant_type = VariantType::I64;
                } else if min >= BigInt::from(i128::min_value())
                    && max <= BigInt::from(i128::max_value())
                {
                    variant_type = VariantType::I128;
                } else {
                    panic::unsupported_discriminant()
                }
            } else {
                let mut counter = BigInt::default();
                let mut constant_counter = 0;
                let mut last_exp: Option<&Expr> = None;

                for variant in data.variants.iter() {
                    if let Fields::Unit = variant.fields {
                        if let Some((_, exp)) = variant.discriminant.as_ref() {
                            match exp {
                                Expr::Lit(lit) => {
                                    let lit = &lit.lit;

                                    let value = match lit {
                                        Lit::Int(value) => {
                                            let value = value.base10_digits();
                                            BigInt::from_str(value).unwrap()
                                        }
                                        _ => panic::unsupported_discriminant(),
                                    };

                                    values.push(BigIntWrapper::from(value.clone()));

                                    counter = value + 1;

                                    last_exp = None;
                                }
                                Expr::Unary(unary) => {
                                    match unary.op {
                                        UnOp::Neg(_) => {
                                            match unary.expr.as_ref() {
                                                Expr::Lit(lit) => {
                                                    let lit = &lit.lit;

                                                    let value = match lit {
                                                        Lit::Int(value) => {
                                                            let value = value.base10_digits();

                                                            -BigInt::from_str(value).unwrap()
                                                        }
                                                        _ => panic::unsupported_discriminant(),
                                                    };

                                                    values.push(BigIntWrapper::from(value.clone()));

                                                    counter = value + 1;

                                                    last_exp = None;
                                                }
                                                Expr::Path(_) => {
                                                    values.push(BigIntWrapper::from((exp, 0)));

                                                    last_exp = Some(exp);
                                                    constant_counter = 1;
                                                }
                                                Expr::Cast(_) | Expr::Binary(_) | Expr::Call(_) => {
                                                    values.push(BigIntWrapper::from((exp, 0)));

                                                    last_exp = Some(exp);
                                                    constant_counter = 1;

                                                    use_constant_counter = true;
                                                }
                                                _ => panic::unsupported_discriminant(),
                                            }
                                        }
                                        _ => panic::unsupported_discriminant(),
                                    }
                                }
                                Expr::Path(_) => {
                                    values.push(BigIntWrapper::from((exp, 0)));

                                    last_exp = Some(exp);
                                    constant_counter = 1;
                                }
                                Expr::Cast(_) | Expr::Binary(_) | Expr::Call(_) => {
                                    values.push(BigIntWrapper::from((exp, 0)));

                                    last_exp = Some(exp);
                                    constant_counter = 1;

                                    use_constant_counter = true;
                                }
                                _ => panic::unsupported_discriminant(),
                            }
                        } else if let Some(exp) = last_exp.as_ref() {
                            values.push(BigIntWrapper::from((*exp, constant_counter)));

                            constant_counter += 1;

                            use_constant_counter = true;
                        } else {
                            values.push(BigIntWrapper::from(counter.clone()));

                            counter += 1;
                        }

                        variant_idents.push(&variant.ident);
                    } else {
                        panic::not_unit_variant();
                    }
                }
            }

            let ordinal = quote! {
                #[inline]
                pub fn ordinal(&self) -> #variant_type {
                    match self {
                        #(
                            Self::#variant_idents => #values,
                        )*
                    }
                }
            };

            let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

            let from_ordinal_unsafe = if data.variants.len() == 1 {
                let variant_idents = &data.variants[0].ident;

                quote! {
                    #[inline]
                    pub unsafe fn from_ordinal_unsafe(_number: #variant_type) -> #name #ty_generics {
                        Self::#variant_idents
                    }
                }
            } else {
                quote! {
                    #[inline]
                    pub unsafe fn from_ordinal_unsafe(number: #variant_type) -> #name #ty_generics {
                        ::core::mem::transmute(number)
                    }
                }
            };

            let from_ordinal = if use_constant_counter {
                quote! {
                    #[inline]
                    pub fn from_ordinal(number: #variant_type) -> Option<#name #ty_generics> {
                        if false {
                            unreachable!()
                        } #( else if number == #values {
                            Some(Self::#variant_idents)
                        } )* else {
                            None
                        }
                    }
                }
            } else {
                quote! {
                    #[inline]
                    pub fn from_ordinal(number: #variant_type) -> Option<#name #ty_generics> {
                        match number{
                            #(
                                #values => Some(Self::#variant_idents),
                            )*
                            _ => None
                        }
                    }
                }
            };

            let variant_count = variant_idents.len();

            let variants = quote! {
                #[inline]
                pub const fn variants() -> [#name #ty_generics; #variant_count] {
                    [#( Self::#variant_idents, )*]
                }
            };

            let variant_count = quote! {
                #[inline]
                pub const fn variant_count() -> usize {
                    #variant_count
                }
            };

            let ordinalize_impl = quote! {
                impl #impl_generics #name #ty_generics #where_clause {
                    #from_ordinal_unsafe

                    #from_ordinal

                    #ordinal

                    #variants

                    #variant_count
                }
            };

            ordinalize_impl.into()
        }
        _ => {
            panic::not_enum();
        }
    }
}

#[proc_macro_derive(Ordinalize)]
pub fn ordinalize_derive(input: TokenStream) -> TokenStream {
    derive_input_handler(syn::parse(input).unwrap())
}
