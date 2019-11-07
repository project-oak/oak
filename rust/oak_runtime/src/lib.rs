// TODO: Plug in memory allocator and depend on https://doc.rust-lang.org/alloc/ to enable use of
// heap.

#![no_std]
#![feature(lang_items)]

use core::panic::PanicInfo;

// See https://doc.rust-lang.org/nomicon/panic-handler.html.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

// See https://doc.rust-lang.org/1.2.0/book/no-stdlib.html.
#[lang = "eh_personality"]
pub extern "C" fn eh_personality() {}

/// An exported placeholder function to check that linking against C++ is successful.
/// It just adds "42" to the provided value and returns it to the caller.
#[no_mangle]
pub extern "C" fn add_magic_number(x: i32) -> i32 {
    x + 42
}
