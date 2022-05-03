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
#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(custom_test_frameworks)]
// As we're in a `no_std` environment, testing requires special handling. This
// approach was inspired by https://os.phil-opp.com/testing/.
#![test_runner(crate::test_runner)]
#![reexport_test_harness_main = "test_main"]

mod logging;
mod memory;
mod serial;

#[macro_use]
extern crate log;

use core::panic::PanicInfo;
use rust_hypervisor_firmware_subset::{boot, paging, pvh};

#[no_mangle]
pub extern "C" fn rust64_start(rdi: &pvh::StartInfo) -> ! {
    logging::init_logging();
    paging::setup();
    memory::init_allocator(rdi);

    if cfg!(test) {
        #[cfg(test)]
        test_main();
        unreachable!("tests should have exited qemu");
    } else {
        main(rdi);
    }
}

fn main(info: &dyn boot::Info) -> ! {
    info!("In main! Boot protocol:  {}", info.name());
    let mut serial = serial::Serial::new();
    runtime::framing::handle_frames(&mut serial).unwrap();
}

// These exit codes are from https://os.phil-opp.com/testing/.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum QemuExitCode {
    Success = 0x10,
    Failed = 0x11,
}

pub fn exit_qemu(exit_code: QemuExitCode) {
    use x86_64::instructions::port::Port;

    unsafe {
        // 0xF4 is the port commonly used for the qemu isa-exit-device.
        // We expect the device to be enabled by the loader at said
        // common address.
        let mut port = Port::new(0xf4);
        port.write(exit_code as u32);
    }
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    error!("PANIC: {}", info);
    exit_qemu(QemuExitCode::Failed);
    loop {}
}

#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[cfg(test)]
fn test_runner(tests: &[&dyn Fn()]) {
    for test in tests {
        test();
    }
    exit_qemu(QemuExitCode::Success);
}
