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
#![feature(core_c_str)]
#![feature(core_ffi_c)]

use core::panic::PanicInfo;

mod hvm_start_info;
#[cfg(all(feature = "multiboot", not(test)))]
mod multiboot;

#[no_mangle]
#[cfg(feature = "multiboot")]
pub extern "C" fn rust64_start(start_info: &multiboot::MultibootInfo, magic: u64) -> ! {
    // The magic constant is specified in multiboot.h.
    // See <https://www.gnu.org/software/grub/manual/multiboot/multiboot.html#Machine-state>
    // for a full specification of the initial machine state.
    // As at this stage we don't even have logging set up, so if the magic does not match,
    // let's just shut down the machine.
    if magic != multiboot::BOOT_MAGIC {
        oak_baremetal_kernel::i8042::shutdown();
    }
    oak_baremetal_kernel::start_kernel(start_info);
}

#[no_mangle]
#[cfg(not(feature = "multiboot"))]
pub extern "C" fn rust64_start(start_info: &hvm_start_info::StartInfo) -> ! {
    // If the magic field doesn't match, we can't be sure we're booting via PVH, so bail out early.
    if start_info.magic != hvm_start_info::BOOT_MAGIC {
        oak_baremetal_kernel::i8042::shutdown();
    }
    oak_baremetal_kernel::start_kernel(start_info);
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("Error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_baremetal_kernel::panic(info);
}
