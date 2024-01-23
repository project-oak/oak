use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Item, ItemFn, Result};

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

    let return_type_error = syn::Error::new(
        syn::spanned::Spanned::span(&entry_fn.sig.output),
        "the entrypoint function should have return type !",
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

        static LOGGER: oak_restricted_kernel_sdk::StderrLogger = oak_restricted_kernel_sdk::StderrLogger {};

        #[no_mangle]
        fn _start() -> ! {
            oak_restricted_kernel_sdk::init(log::LevelFilter::Debug);
            #entry_fn_name();
        }

        #[alloc_error_handler]
        fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
            oak_restricted_kernel_sdk::alloc_error_handler(layout);
        }

        #[panic_handler]
        fn panic(info: &core::panic::PanicInfo) -> ! {
            oak_restricted_kernel_sdk::panic_handler(info);
        }
    };
    TokenStream::from(generated)
}
