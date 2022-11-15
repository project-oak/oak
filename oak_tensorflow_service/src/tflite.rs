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

use alloc::{vec, vec::Vec};
use anyhow::{anyhow, Context};
use log::{log, Level};

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

// TODO(#3297): Decide the TensorFlow model format to be passed as `model_bytes`.
#[link(name = "tflite_micro", kind = "static")]
extern "C" {
    /// Initializes the TensorFlow model and returns a corresponding error code.
    ///
    /// Memory area that will be used by the TFLM memory manager is defined by `tensor_arena_bytes`:
    /// <https://github.com/tensorflow/tflite-micro/blob/main/tensorflow/lite/micro/docs/memory_management.md>
    ///
    /// This function returns a buffer size value in the `output_buffer_len_ptr`. This buffer should
    /// be allocated before calling `tflite_run` to store inference results.
    fn tflite_init(
        model_bytes_ptr: *const u8,
        model_bytes_len: usize,
        tensor_arena_bytes_ptr: *mut u8,
        tensor_arena_bytes_len: usize,
        output_buffer_len_ptr: *mut usize,
    ) -> i32;

    /// Performs inference on `input_bytes_ptr` and pass inference result to `output_bytes_ptr` and
    /// returns an error code.
    ///
    /// The value in the `output_bytes_len_ptr` cannot be bigger than the value in
    /// `output_buffer_len_ptr` from `tflite_init`.
    fn tflite_run(
        input_bytes_ptr: *const u8,
        input_bytes_len: usize,
        output_bytes_ptr: *mut u8,
        output_bytes_len_ptr: *mut usize,
    ) -> i32;
}

// TODO(#3297): Use 8GiB or 10GiB arena sizes.
const TENSOR_ARENA_SIZE: usize = 1024 * 1024 * 1024;

#[derive(Default)]
pub struct TfliteModel {
    tensor_arena: Vec<u8>,
    /// Defines a output buffer length that should be preallocated before calling `tflite_run`.
    /// This value is only initialized after `initialize` function because TFLite should return the
    /// `output_buffer_len`.
    /// If the value is `None` then `TfliteModel` hasn't been initialized yet.
    output_buffer_len: Option<usize>,
}

impl TfliteModel {
    pub fn new() -> Self {
        let tensor_arena = vec![0; TENSOR_ARENA_SIZE];
        Self {
            tensor_arena,
            output_buffer_len: None,
        }
    }

    pub fn initialize(&mut self, model_bytes: &[u8]) -> anyhow::Result<()> {
        log!(Level::Info, "Initializing the TFLite model");
        if self.output_buffer_len.is_some() {
            return Err(anyhow!("TFLite model has already been initialized"));
        }

        let model_bytes_len = model_bytes.len();
        let tensor_arena_len = self.tensor_arena.len();
        let mut output_buffer_len = 0usize;

        let result_code = unsafe {
            tflite_init(
                model_bytes.as_ptr(),
                model_bytes_len,
                self.tensor_arena.as_mut_ptr(),
                tensor_arena_len,
                &mut output_buffer_len,
            )
        };
        if result_code == 0 {
            self.output_buffer_len = Some(output_buffer_len);
            log!(
                Level::Info,
                "TFLite model has been successfully initialized"
            );
            Ok(())
        } else {
            Err(anyhow!(
                "couldn't initialize TFLite model, code: {}",
                result_code
            ))
        }
    }

    pub fn run(&mut self, input_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        log!(Level::Info, "Running TFLite inference");
        let output_buffer_len = self
            .output_buffer_len
            .context("running inference on a non-initialized TensorFlow model")?;

        let input_bytes_len = input_bytes.len();
        let mut output_buffer = vec![0; output_buffer_len];
        let mut output_bytes_len = 0usize;

        let result_code = unsafe {
            tflite_run(
                input_bytes.as_ptr(),
                input_bytes_len,
                output_buffer.as_mut_ptr(),
                &mut output_bytes_len,
            )
        };
        if result_code == 0 {
            if output_bytes_len <= output_buffer_len {
                log!(Level::Info, "TFLite inference has run successfully");
                Ok(output_buffer[..output_bytes_len].to_vec())
            } else {
                // Panicking since if the output bytes length is bigger than the output buffer
                // length, then there is a potential for memory corruption and we can't rely on any
                // of the Rust memory safety assumptions.
                panic!("output bytes length is bigger than the output buffer length");
            }
        } else {
            Err(anyhow!(
                "couldn't run TFLite inference, code: {}",
                result_code
            ))
        }
    }
}
