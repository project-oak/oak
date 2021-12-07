mod models;

mod hash_enum;
mod hash_struct;

use super::TraitHandler;

use crate::panic;
use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Meta};
use crate::Trait;

use hash_enum::HashEnumHandler;
use hash_struct::HashStructHandler;

pub struct HashHandler;

impl TraitHandler for HashHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        match ast.data {
            Data::Struct(_) => {
                HashStructHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Enum(_) => {
                HashEnumHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Union(_) => panic::trait_not_support_union(Trait::Hash),
        }
    }
}
