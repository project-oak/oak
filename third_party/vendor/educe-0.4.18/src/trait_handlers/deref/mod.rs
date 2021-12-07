mod models;

mod deref_enum;
mod deref_struct;

use super::TraitHandler;

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Meta};
use crate::Trait;

use deref_enum::DerefEnumHandler;
use deref_struct::DerefStructHandler;

pub struct DerefHandler;

impl TraitHandler for DerefHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        match ast.data {
            Data::Struct(_) => {
                DerefStructHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Enum(_) => {
                DerefEnumHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Union(_) => panic::trait_not_support_union(Trait::Deref),
        }
    }
}
