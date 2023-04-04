//
// Copyright 2023 The Project Oak Authors
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

use core::ffi::c_void;

use alloc::{vec, vec::Vec};
use anyhow::{anyhow, Context};
use log::{log, Level};
use oak_restricted_kernel_api::syscall::mmap;
use oak_restricted_kernel_interface::syscalls::{MmapFlags, MmapProtection};

// TODO(#3297): Don't use null terminated and use `string_view` instead.
/// Prints `message` to the debug Restricted Kernel logs.
/// These logs are being sent outside of the Trusted Execution Environment.
#[no_mangle]
pub unsafe extern "C" fn oak_log_debug(message_ptr: *const core::ffi::c_char, message_len: usize) {
    let message_bytes =
        unsafe { alloc::slice::from_raw_parts(message_ptr as *const u8, message_len) };
    if let Ok(message_string) = core::str::from_utf8(message_bytes) {
        log!(Level::Debug, "tflite_micro: {}", message_string);
    } else {
        log!(
            Level::Debug,
            "tflite_micro: Couldn't parse a UTF-8 string: {:?}",
            message_bytes
        );
    }
}

// #[no_mangle]
// pub unsafe extern "C" fn posix_memalign(res: *mut *mut core::ffi::c_void, align: usize, len: usize) -> core::ffi::c_int {
// 	// if (align < sizeof(void *)) return EINVAL;
// 	// void *mem = aligned_alloc(align, len);
// 	// if (!mem) return errno;
// 	// *res = mem;
//     log!(
//         Level::Info,
//         "Running posix_memalign, align: {}, len: {}", align, len,
//     );
//     return 0;
// }

// TODO(#3297): Decide the TensorFlow model format to be passed as `model_bytes`.
#[link(name = "iree", kind = "static")]
extern "C" {
    /// Initializes the TensorFlow model and returns a corresponding error code.
    ///
    /// Memory area that will be used by the TFLM memory manager is defined by `tensor_arena_bytes`:
    /// <https://github.com/tensorflow/tflite-micro/blob/main/tensorflow/lite/micro/docs/memory_management.md>
    ///
    /// This function returns a buffer size value in the `output_buffer_len_ptr`. This buffer should
    /// be allocated before calling `tflite_run` to store inference results.
    // fn iree_init(
        // model_bytes_ptr: *const u8,
        // model_bytes_len: usize,
        // tensor_arena_bytes_ptr: *mut u8,
        // tensor_arena_bytes_len: usize,
        // output_buffer_len_ptr: *mut usize,
    // ) -> i32;

    /// Performs inference on `input_bytes_ptr` and pass inference result to `output_bytes_ptr` and
    /// returns an error code.
    ///
    /// The value in the `output_bytes_len_ptr` cannot be bigger than the value in
    /// `output_buffer_len_ptr` from `tflite_init`.
    fn iree_run(
        input_bytes_ptr: *const u8,
        input_bytes_len: usize,
        output_bytes_ptr: *mut u8,
        output_bytes_len_ptr: *mut usize,
    ) -> i32;
}

// TODO(#3297): Use 8GiB or 10GiB arena sizes.
const TENSOR_ARENA_SIZE: isize = 1024 * 1024 * 1024;

pub struct TfliteModel {
    // tensor_arena: &'static mut [u8],
    /// TFLite model binary representation.
    /// Rust needs to keep ownership of the model, because the C++ code just uses it as a
    /// reference.
    model_bytes: Vec<u8>,
    /// Defines a output buffer length that should be preallocated before calling `tflite_run`.
    /// This value is only initialized after `initialize` function because TFLite should return the
    /// `output_buffer_len`.
    /// If the value is `None` then `TfliteModel` hasn't been initialized yet.
    output_buffer_len: Option<usize>,
}

impl Default for TfliteModel {
    fn default() -> Self {
        Self::new()
    }
}

impl TfliteModel {
    pub fn new() -> Self {
        // // Allocate memory. Both Oak Restricted Kernel and Linux have similar enough `mmap()`
        // // semantics for this to work.
        // let mem = mmap(
        //     // We don't particularly care where the allocation lands, but let's place it at the 64
        //     // GiB mark to ensure we won't reasonably have the heap running into it.
        //     Some(0x10_0000_0000 as *const c_void),
        //     TENSOR_ARENA_SIZE,
        //     MmapProtection::PROT_READ | MmapProtection::PROT_WRITE,
        //     MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE,
        //     -1,
        //     0,
        // )
        // .expect("failed to allocate memory for tensor arena");
        Self {
            // tensor_arena: mem,
            model_bytes: vec![],
            output_buffer_len: None,
        }
    }

    pub fn initialize(&mut self, model_bytes: &[u8]) -> anyhow::Result<()> {
        log!(Level::Info, "Initializing the IREE model");
        let result_code = unsafe {
            0
            // iree_init()
        };
        let output_buffer_len = 18520usize;
        // if self.output_buffer_len.is_some() {
        //     return Err(anyhow!("TFLite model has already been initialized"));
        // }

        // // Save a copy of the TFLite model.
        // self.model_bytes = model_bytes.to_vec();

        // let mut output_buffer_len = 0usize;
        // let result_code = unsafe {
        //     tflite_init(
        //         self.model_bytes.as_ptr(),
        //         self.model_bytes.len(),
        //         self.tensor_arena.as_mut_ptr(),
        //         TENSOR_ARENA_SIZE as usize,
        //         &mut output_buffer_len,
        //     )
        // };
        if result_code == 0 {
            self.output_buffer_len = Some(output_buffer_len);
            log!(
                Level::Info,
                "IREE model has been successfully initialized"
            );
            Ok(())
        } else {
            Err(anyhow!(
                "couldn't initialize IREE model, code: {}",
                result_code
            ))
        }
    }

    pub fn run(&mut self, input_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        log!(Level::Info, "Running IREE inference");
        let output_buffer_len = self
            .output_buffer_len
            .context("running inference on a non-initialized IREE model")?;

        let mut output_buffer = vec![0; output_buffer_len];
        let mut output_bytes_len = 0usize;
        let result_code = unsafe {
            iree_run(
                input_bytes.as_ptr(),
                input_bytes.len(),
                output_buffer.as_mut_ptr(),
                &mut output_bytes_len,
            )
        };
        if result_code == 0 {
            if output_bytes_len <= output_buffer_len {
                log!(Level::Info, "IREE inference has run successfully");
                Ok(output_buffer[..output_bytes_len].to_vec())
            } else {
                // Panicking since if the output bytes length is bigger than the output buffer
                // length, then there is a potential for memory corruption and we can't rely on any
                // of the Rust memory safety assumptions.
                panic!("output bytes length of {} is bigger than the output buffer length of {}", output_bytes_len, output_buffer_len);
            }
        } else {
            log!(Level::Error, "couldn't run IREE inference, code: {}", result_code);
            Err(anyhow!(
                "couldn't run IREE inference, code: {}",
                result_code
            ))
        }
    }
}
