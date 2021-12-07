mod models;

mod partial_ord_enum;
mod partial_ord_struct;

use super::TraitHandler;

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Meta};
use crate::Trait;

use partial_ord_enum::PartialOrdEnumHandler;
use partial_ord_struct::PartialOrdStructHandler;

pub struct PartialOrdHandler;

impl TraitHandler for PartialOrdHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        match ast.data {
            Data::Struct(_) => {
                PartialOrdStructHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Enum(_) => {
                PartialOrdEnumHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Union(_) => panic::trait_not_support_union(Trait::PartialOrd),
        }
    }
}
