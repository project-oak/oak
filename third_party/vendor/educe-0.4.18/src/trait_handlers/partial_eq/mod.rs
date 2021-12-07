mod models;

mod partial_eq_enum;
mod partial_eq_struct;

use super::TraitHandler;

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Meta};
use crate::Trait;

use partial_eq_enum::PartialEqEnumHandler;
use partial_eq_struct::PartialEqStructHandler;

pub struct PartialEqHandler;

impl TraitHandler for PartialEqHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        match ast.data {
            Data::Struct(_) => {
                PartialEqStructHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Enum(_) => {
                PartialEqEnumHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Union(_) => panic::trait_not_support_union(Trait::PartialEq),
        }
    }
}
