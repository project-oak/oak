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

//! Various utilities like loggers, allocators, timers, etc.

use core::fmt::Write;

pub use log;
pub use oak_core::*;
pub use oak_enclave_runtime_support::heap;
use oak_restricted_kernel_interface::syscall::{fsync, write};

pub struct Stderr {}

impl Stderr {
    const STDERR_FD: i32 = 2;

    pub fn flush() {
        fsync(Self::STDERR_FD).unwrap();
    }
}

impl core::fmt::Write for Stderr {
    fn write_str(&mut self, s: &str) -> Result<(), core::fmt::Error> {
        let buf = s.as_bytes();
        let mut written = 0;
        while written < s.len() {
            written += write(Self::STDERR_FD, &buf[written..]).unwrap();
        }

        Ok(())
    }
}

/// [`log::Log`] implementation that outputs logs on standard error.
///
/// Implicitly declared as the global logger when using the
/// [`crate::entrypoint`] macro.
pub struct StderrLogger {}

impl log::Log for StderrLogger {
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

/// Provides a default implementation for [`alloc_error_handler`] attribute.
///
/// This handler is declared implicitly when using the [`crate::entrypoint`]
/// macro.
///
/// [`alloc_error_handler`]: <https://github.com/rust-lang/rust/issues/51540>
pub fn alloc_error_handler(layout: ::core::alloc::Layout) -> ! {
    panic!("error allocating memory: {:#?}", layout);
}

/// Provides a default implementation for [`panic_handler`] attribute.
///
/// This handler is declared implicitly when using the [`crate::entrypoint`]
/// macro.
///
/// [`panic_handler`]: <https://doc.rust-lang.org/reference/runtime.html#the-panic_handler-attribute>
pub fn panic_handler(info: &core::panic::PanicInfo) -> ! {
    log::error!("PANIC: {}", info);
    oak_restricted_kernel_interface::syscall::exit(-1);
}
