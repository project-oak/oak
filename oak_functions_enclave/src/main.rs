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

extern crate alloc;

use alloc::{boxed::Box, sync::Arc};
use core::{fmt::Write, panic::PanicInfo};
use linked_list_allocator::LockedHeap;
use log::info;
use oak_remote_attestation_amd::PlaceholderAmdAttestationGenerator;
use oak_restricted_kernel_api::FileDescriptorChannel;
use oak_restricted_kernel_interface::syscalls::{MmapFlags, MmapProtection};

#[global_allocator]
static ALLOCATOR: LockedHeap = LockedHeap::empty();

static LOGGER: Logger = Logger {};

struct Stderr {}

impl Stderr {
    const STDERR_FD: i32 = 2;

    fn flush() {
        oak_restricted_kernel_api::syscall::fsync(Self::STDERR_FD).unwrap();
    }
}

impl core::fmt::Write for Stderr {
    fn write_str(&mut self, s: &str) -> Result<(), core::fmt::Error> {
        let buf = s.as_bytes();
        let mut written = 0;
        while written < s.len() {
            written += oak_restricted_kernel_api::syscall::write(Self::STDERR_FD, &buf[written..])
                .unwrap();
        }

        Ok(())
    }
}

struct Logger {}
impl log::Log for Logger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        writeln!(Stderr {}, "{}: {}", record.level(), record.args()).unwrap();
    }

    fn flush(&self) {
        Stderr::flush();
    }
}

#[no_mangle]
pub extern "C" fn fmod(a: f64, b: f64) -> f64 {
    libm::fmod(a, b)
}

#[no_mangle]
pub extern "C" fn fmodf(a: f32, b: f32) -> f32 {
    libm::fmodf(a, b)
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("PANIC: {}", info);
    oak_restricted_kernel_api::syscall::exit(-1);
}

#[no_mangle]
fn _start() -> ! {
    log::set_logger(&LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Debug);

    let mem = oak_restricted_kernel_api::syscall::mmap(
        core::ptr::null(),
        10 * (1 << 20),
        MmapProtection::PROT_READ | MmapProtection::PROT_WRITE,
        MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE,
        -1,
        0,
    )
    .unwrap();
    unsafe {
        ALLOCATOR.lock().init(mem.as_mut_ptr(), 10 * (1 << 20));
    }

    main();
    oak_restricted_kernel_api::syscall::exit(0);
}

pub fn main() {
    info!("In main!");
    let service = oak_functions_service::OakFunctionsService::new(Arc::new(
        PlaceholderAmdAttestationGenerator,
    ));
    let server = oak_functions_service::schema::OakFunctionsServer::new(service);
    oak_channel::server::start_blocking_server(Box::<FileDescriptorChannel>::default(), server)
        .expect("server encountered an unrecoverable error");
}
