//
// Copyright 2022 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use proc_macro::TokenStream;
use quote::quote;
use syn::{Item, ItemFn, Result, parse_macro_input};

#[proc_macro_attribute]
pub fn entrypoint(_attr: TokenStream, entry: TokenStream) -> TokenStream {
    let entry_item = parse_macro_input!(entry as syn::Item);
    match validate_type_signature(entry_item) {
        Ok(entry_fn) => process_entry_fn(entry_fn),
        Err(error) => error.to_compile_error().into(),
    }
}

fn validate_type_signature(entry_item: Item) -> Result<ItemFn> {
    let entry_fn: ItemFn = match entry_item {
        syn::Item::Fn(entry_fn) => Ok(entry_fn),
        _ => Err(syn::Error::new(
            syn::spanned::Spanned::span(&entry_item),
            "the entrypoint macro can only be applied to functions",
        )),
    }?;

    if !entry_fn.sig.inputs.is_empty() {
        return Err(syn::Error::new(
            syn::spanned::Spanned::span(&entry_fn.sig.inputs),
            "the entrypoint function must not take arguments",
        ));
    }

    let return_type_error = syn::Error::new(
        syn::spanned::Spanned::span(&entry_fn.sig.output),
        "the entrypoint function must have return type !",
    );
    match &entry_fn.sig.output {
        syn::ReturnType::Default => Err(return_type_error),
        syn::ReturnType::Type(_, return_type) => match **return_type {
            syn::Type::Never(_) => Ok(entry_fn),
            _ => Err(return_type_error),
        },
    }
}

fn process_entry_fn(entry_fn: ItemFn) -> TokenStream {
    let entry_fn_name = &entry_fn.sig.ident;

    let generated = quote! {
        #entry_fn

        #[global_allocator]
        static ALLOCATOR: oak_restricted_kernel_sdk::utils::heap::LockedGrowableHeap = oak_restricted_kernel_sdk::utils::heap::LockedGrowableHeap::empty();

        static LOGGER: oak_restricted_kernel_sdk::utils::StderrLogger = oak_restricted_kernel_sdk::utils::StderrLogger {};

        #[unsafe(no_mangle)]
        fn _start() -> ! {
            oak_restricted_kernel_sdk::utils::log::set_logger(&LOGGER).expect("failed to set logger");
            // Set the default. Applications may overwrite the log level by calling
            // this function again.
            oak_restricted_kernel_sdk::utils::log::set_max_level(
                // Performance optimization. The current restricted kernel logger
                // logs over a serial port. This is slow in general, and extremely
                // slow on SEV-SNP.
                if cfg!(debug_assertions) {
                    oak_restricted_kernel_sdk::utils::log::LevelFilter::Debug
                } else {
                    oak_restricted_kernel_sdk::utils::log::LevelFilter::Warn
                }
            );
            oak_restricted_kernel_sdk::utils::log::info!("In main!");
            #entry_fn_name();
        }

        #[alloc_error_handler]
        fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
            oak_restricted_kernel_sdk::utils::alloc_error_handler(layout);
        }

        #[panic_handler]
        fn panic(info: &core::panic::PanicInfo) -> ! {
            oak_restricted_kernel_sdk::utils::panic_handler(info);
        }
    };
    TokenStream::from(generated)
}
