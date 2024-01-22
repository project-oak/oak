use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Item, Result};

#[proc_macro_attribute]
pub fn entrypoint(_attr: TokenStream, input: TokenStream) -> TokenStream {
    let input_item = parse_macro_input!(input as syn::Item);

    match process_oak_main(input_item) {
        Ok(output) => output,
        Err(error) => error.to_compile_error().into(),
    }
}

fn process_oak_main(input_item: Item) -> Result<TokenStream> {
    let input_fn = match input_item {
        syn::Item::Fn(fn_item) => Ok(fn_item),
        _ => Err(syn::Error::new(
            syn::spanned::Spanned::span(&input_item),
            "the oak_main macro can only be applied to functions",
        )),
    }?;

    let input_fn_name = &input_fn.sig.ident;

    let generated = quote! {
        #input_fn

        static LOGGER: oak_restricted_kernel_sdk::StderrLogger = oak_restricted_kernel_sdk::StderrLogger {};

        #[no_mangle]
        fn _start() -> ! {
            log::set_logger(&LOGGER).unwrap();
            log::set_max_level(log::LevelFilter::Debug);
            oak_enclave_runtime_support::init();
            log::info!("In main!");
            #input_fn_name();
        }

        #[alloc_error_handler]
        fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
            panic!("error allocating memory: {:#?}", layout);
        }

        #[panic_handler]
        fn panic(info: &core::panic::PanicInfo) -> ! {
            log::error!("PANIC: {}", info);
            oak_restricted_kernel_interface::syscall::exit(-1);
        }
    };

    Ok(TokenStream::from(generated))
}
