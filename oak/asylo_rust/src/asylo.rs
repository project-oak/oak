//
// Copyright 2019 The Project Oak Authors
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

use core::alloc::Layout;
use core::panic::PanicInfo;

pub use rust::asylo::thread;
pub use rust::asylo::mutex;

#[link(name = "sgx_trts")]
extern "C" {
    // SGX-enabled abort function that causes an undefined instruction (`UD2`) to be executed, which
    // terminates the enclave execution.
    //
    // The C type of this function is `extern "C" void abort(void) __attribute__(__noreturn__);`
    //
    // See https://github.com/intel/linux-sgx/blob/d166ff0c808e2f78d37eebf1ab614d944437eea3/sdk/trts/linux/trts_pic.S#L565.
    fn abort() -> !;
}

// See https://doc.rust-lang.org/nomicon/panic-handler.html.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    unsafe { abort() }
}

// Define what happens in an Out Of Memory (OOM) condition.
#[alloc_error_handler]
fn alloc_error(_layout: Layout) -> ! {
    unsafe { abort() }
}
