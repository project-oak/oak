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

pub mod thread;
pub mod mutex;
pub mod allocator;

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
