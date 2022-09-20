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

extern crate alloc;

use alloc::boxed::Box;
use core::panic::PanicInfo;
use log::info;
use oak_baremetal_communication_channel::Channel;

mod asm;
mod bootparam;

#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, rsi: &bootparam::BootParams) -> ! {
    let channel = oak_baremetal_kernel::start_kernel(rsi);
    info!("In main!");
    start_echo_server(channel)
}

fn start_echo_server(mut channel: Box<dyn Channel>) -> ! {
    // Starts an echo server that reads single bytes from the channel and writes
    // them back.
    #[cfg(feature = "raw_server")]
    {
        use alloc::{vec, vec::Vec};
        const MESSAGE_SIZE: usize = 1;

        loop {
            let bytes = {
                let mut bytes: Vec<u8> = vec![0; MESSAGE_SIZE];
                channel.read(&mut bytes).expect("Couldn't read bytes");
                bytes
            };
            channel.write(&bytes).expect("Couldn't write bytes");
        }
    }
    // Starts an echo server that uses the Oak communication channel:
    // https://github.com/project-oak/oak/blob/main/experimental/oak_baremetal_channel/SPEC.MD
    #[cfg(all(feature = "idl_server", not(feature = "raw_server")))]
    {
        let runtime = oak_echo_runtime::RuntimeImplementation::new();
        let service = oak_echo_runtime::schema::EchoRuntime::serve(runtime);
        oak_baremetal_communication_channel::server::start_blocking_server(channel, service)
            .expect("Runtime encountered an unrecoverable error");
    }
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("Error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_baremetal_kernel::panic(info);
}
