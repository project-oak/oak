mod models;

mod debug_enum;
mod debug_struct;
mod debug_union;

use super::TraitHandler;

use crate::proc_macro2::TokenStream;
use crate::syn::{Data, DeriveInput, Meta};
use crate::Trait;

use debug_enum::DebugEnumHandler;
use debug_struct::DebugStructHandler;
use debug_union::DebugUnionHandler;

pub struct DebugHandler;

impl TraitHandler for DebugHandler {
    fn trait_meta_handler(
        ast: &DeriveInput,
        tokens: &mut TokenStream,
        traits: &[Trait],
        meta: &Meta,
    ) {
        match ast.data {
            Data::Struct(_) => {
                DebugStructHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Enum(_) => {
                DebugEnumHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
            Data::Union(_) => {
                DebugUnionHandler::trait_meta_handler(ast, tokens, traits, meta);
            }
        }
    }
}
