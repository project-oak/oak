//
// Copyright 2024 The Project Oak Authors
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

use alloc::boxed::Box;
use core::{
    ffi::{c_size_t, c_void},
    slice,
};

use crate::payload::Process;

pub fn syscall_unstable_switch_proccess(buf: *mut c_void, count: c_size_t) -> ! {
    // We should validate that the pointer and count are valid, as these come from userspace and
    // therefore are not to be trusted, but right now everything is in kernel space so there is
    // nothing to check.
    let elf_binary_buffer = unsafe { slice::from_raw_parts(buf as *mut u8, count) };

    // Copy the ELF file into kernel space.
    let copied_elf_binary = elf_binary_buffer.to_vec();

    let application = crate::payload::Application::new(copied_elf_binary.into_boxed_slice())
        .expect("failed to parse application");

    // Ensure the new process is not dropped.
    let process = Box::leak(Box::new(
        // Safety: application is assumed to be a valid ELF file.
        unsafe { Process::from_application(&application).expect("failed to create process") },
    ));

    process.execute()
}
