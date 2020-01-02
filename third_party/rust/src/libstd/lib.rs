#![no_std]

#![feature(lang_items)]
#![feature(allocator_api)]
#![feature(alloc_prelude)]
#![feature(alloc_error_handler)]
#![feature(fn_traits)]
#![feature(rustc_private)]
#![feature(never_type)]
#![feature(box_syntax)]
#![feature(int_error_internals)]
#![feature(array_error_internals)]
#![feature(char_error_internals)]

extern crate alloc;
extern crate core;
extern crate libc;

pub use alloc::prelude::v1::*;

pub mod error;
pub mod io;
pub mod asylo;
