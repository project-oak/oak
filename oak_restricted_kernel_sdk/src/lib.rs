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

#![cfg_attr(not(test), no_std)]

extern crate alloc;

mod channel;
mod dice;
mod logging;

pub use channel::FileDescriptorChannel;
pub use dice::*;
pub use logging::StderrLogger;
use logging::STDERR_LOGGER;
pub use oak_restricted_kernel_sdk_proc_macro::entrypoint;

/// Initialization function that sets up the allocator and logger.
pub fn init(log_level: log::LevelFilter) {
    log::set_logger(&STDERR_LOGGER).expect("failed to set logger");
    log::set_max_level(log_level);
    oak_enclave_runtime_support::init();
}

pub fn alloc_error_handler(layout: ::core::alloc::Layout) -> ! {
    panic!("error allocating memory: {:#?}", layout);
}

pub fn panic_handler(info: &core::panic::PanicInfo) -> ! {
    log::error!("PANIC: {}", info);
    oak_restricted_kernel_interface::syscall::exit(-1);
}
