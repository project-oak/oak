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

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

mod logging;
mod memory;
mod serial;

#[macro_use]
extern crate log;

#[cfg(not(test))]
use core::panic::PanicInfo;
use rust_hypervisor_firmware_subset::{boot, paging, pvh};

#[no_mangle]
pub extern "C" fn rust64_start(rdi: &pvh::StartInfo) -> ! {
    unsafe {
        logging::init_logging();
    }
    paging::setup();
    memory::init_allocator(rdi);

    main(rdi)
}

fn main(info: &dyn boot::Info) -> ! {
    info!("In main! Boot protocol:  {}", info.name());
    let mut serial = serial::Serial::new();
    runtime::echo::echo(&mut serial).unwrap();
}

#[cfg(not(test))]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    error!("PANIC: {}", info);
    loop {}
}
