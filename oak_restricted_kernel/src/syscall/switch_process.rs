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
    ffi::{c_size_t, c_void},
    slice,
};

pub fn syscall_unstable_switch_proccess(buf: *mut c_void, count: c_size_t) -> ! {
    // We should validate that the pointer and count are valid, as these come from userspace and
    // therefore are not to be trusted, but right now everything is in kernel space so there is
    // nothing to check.
    let elf_binary_buffer = unsafe { slice::from_raw_parts(buf as *mut u8, count) };

    // Copy the elf file into kernel space.
    let copied_elf_binary = elf_binary_buffer.to_vec();

    let application = crate::payload::Application::new(copied_elf_binary.into_boxed_slice())
        .expect("failed to parse application");

    {
        let program_headers = unsafe { crate::elf::get_phdrs(x86_64::VirtAddr::new(0x20_0000)) };
        log::info!("creating new page table");
        let new_page_table = crate::mm::init_paging(program_headers).unwrap();
        log::info!("swapping in new page table");
        let _prev_page_table = crate::PAGE_TABLES.lock().replace(new_page_table);
    };

    // Safety: we've loaded the Restricted Application. Whether that's valid or not is no longer
    // under the kernel's control.
    unsafe { application.run() }
}
