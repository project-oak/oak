mod models;

mod ord_enum;
mod ord_struct;

use super::TraitHandler;

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Meta};
use crate::Trait;

use ord_enum::OrdEnumHandler;
use ord_struct::OrdStructHandler;

pub struct OrdHandler;

impl TraitHandler for OrdHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        match ast.data {
            Data::Struct(_) => {
                OrdStructHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Enum(_) => {
                OrdEnumHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Union(_) => panic::trait_not_support_union(Trait::Ord),
        }
    }
}
