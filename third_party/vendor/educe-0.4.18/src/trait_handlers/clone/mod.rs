mod models;

mod clone_enum;
mod clone_struct;
mod clone_union;

use super::TraitHandler;

use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Meta};
use crate::Trait;

use clone_enum::CloneEnumHandler;
use clone_struct::CloneStructHandler;
use clone_union::CloneUnionHandler;

pub struct CloneHandler;

impl TraitHandler for CloneHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        match ast.data {
            Data::Struct(_) => {
                CloneStructHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Enum(_) => {
                CloneEnumHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Union(_) => {
                CloneUnionHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
        }
    }
}
