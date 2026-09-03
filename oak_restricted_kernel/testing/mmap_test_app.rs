//
// Copyright 2026 The Project Oak Authors
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

//! Guest half of the `mmap` protection test.
//!
//! Asks for mappings with several protection bit combinations and prints what
//! it got back, so a wrong answer reaches the host instead of panicking here.

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;

use core::fmt::{Display, Write};

use oak_restricted_kernel_interface::{
    Errno,
    syscall::mmap,
    syscalls::{MmapFlags, MmapProtection},
};
use oak_restricted_kernel_sdk::{entrypoint, utils::Stderr};

/// Marks the lines the host reads, since the console also carries kernel logs.
pub const REPORT_PREFIX: &str = "mmap_test: ";

/// Printed once every request has been made.
pub const READY_MARKER: &str = "mmap test done";

/// The kernel's `mmap` works in 2 MiB chunks.
const SIZE: isize = 2 * 1024 * 1024;

/// Requests an anonymous private mapping of [`SIZE`] bytes.
fn request(prot: MmapProtection) -> Result<&'static mut [u8], Errno> {
    mmap(None, SIZE, prot, MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE, -1, 0)
}

fn report(name: &str, outcome: impl Display) {
    writeln!(Stderr {}, "{REPORT_PREFIX}{name}={outcome}").unwrap();
}

#[entrypoint]
fn mmap_test() -> ! {
    // Positive control: the refusals below mean nothing if `mmap` never works.
    match request(MmapProtection::PROT_READ | MmapProtection::PROT_WRITE) {
        Ok(page) => {
            // Check the page works. Volatile, or the store gets optimised away.
            // SAFETY: the mapping is readable/writable, and there is no
            // multi-threading, so nothing else aliases it.
            unsafe { core::ptr::write_volatile(page.as_mut_ptr(), 0xA5) };
            report("rw", "mapped,writable");
        }
        Err(errno) => report("rw", errno),
    }

    // Ring 3 must not get an executable page, whatever else it asks for.
    for (name, prot) in [
        ("rwx", MmapProtection::PROT_READ | MmapProtection::PROT_WRITE | MmapProtection::PROT_EXEC),
        ("rx", MmapProtection::PROT_READ | MmapProtection::PROT_EXEC),
        ("x", MmapProtection::PROT_EXEC),
    ] {
        match request(prot) {
            Ok(_) => report(name, "mapped"),
            Err(errno) => report(name, errno),
        }
    }

    writeln!(Stderr {}, "{READY_MARKER}").unwrap();
    Stderr::flush();

    loop {
        core::hint::spin_loop();
    }
}
