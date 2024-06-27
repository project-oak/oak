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

use core::{
    ffi::{c_size_t, c_ssize_t, c_void},
    slice,
};

use oak_restricted_kernel_interface::Errno;

use crate::processes::Process;

pub fn syscall_unstable_create_proccess(buf: *mut c_void, count: c_size_t) -> c_ssize_t {
    // Safety: we should validate that the pointer and count are valid, as these
    // come from userspace and therefore are not to be trusted, but right now
    // everything is in kernel space so there is nothing to check.
    let elf_binary_buffer = unsafe { slice::from_raw_parts(buf as *mut u8, count) };
    match unstable_create_proccess(elf_binary_buffer) {
        // Safety: [`unstable_create_proccess`] does not return if succesful.
        Ok(_) => unsafe {
            core::hint::unreachable_unchecked();
        },
        Err(err) => err as isize,
    }
}

fn unstable_create_proccess(buf: &[u8]) -> Result<!, Errno> {
    // Copy the ELF file into kernel space.
    let copied_elf_binary: alloc::vec::Vec<u8> = buf.to_vec();

    let elf_executeable =
        crate::processes::ElfExecuteable::new(copied_elf_binary.into_boxed_slice())
            .inspect_err(|err| log::error!("failed to parse application elf file: {:?}", err))
            .map_err(|_| Errno::EINVAL)?;
    // Safety: application is assumed to be a valid ELF file, syscalls are setup.
    unsafe {
        Process::from_elf_executeable(&elf_executeable)
            .inspect_err(|err| log::error!("failed to load elf file into memory: {:?}", err))
            .map_err(|_| Errno::EINVAL)?
            .execute()
            .inspect_err(|err| log::error!("failed start process: {:?}", err))
            .map_err(|_| Errno::EINVAL)?
    }
}
