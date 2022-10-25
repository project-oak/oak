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
        log!(Level::Debug, "{}", message_string);
    } else {
        log!(
            Level::Debug,
            "Couldn't parse a UTF-8 string: {:?}",
            message_bytes
        );
    }
}

// TODO(#3297): Decide the TensorFlow model format to be passed as `model_bytes`.
#[link(name = "tflite-micro", kind = "static")]
extern "C" {
    /// Initializes the TensorFlow model and returns a corresponding error code.
    ///
    /// Memory area that will be used by the TFLM memory manager is defined by `tensor_arena_bytes`:
    /// <https://github.com/tensorflow/tflite-micro/blob/main/tensorflow/lite/micro/docs/memory_management.md>
    ///
    /// This function returns a buffer size value in the `output_buffer_len`. This buffer should be
    /// allocated before calling `tflite_run` to store inference results.
    fn tflite_init(
        model_bytes: *const u8,
        model_bytes_len: usize,
        tensor_arena_bytes: *const u8,
        tensor_arena_bytes_len: usize,
        output_buffer_len: *mut usize,
    ) -> i32;

    /// Performs inference on `input_bytes` and pass inference result to `output_bytes` and returns
    /// an error code.
    fn tflite_run(
        input_bytes: *const u8,
        input_bytes_len: usize,
        output_bytes: *mut u8,
        output_bytes_len: *mut usize,
    ) -> i32;
}

// TODO(#3297): Use 8GiB or 10GiB arena sizes.
const TENSOR_ARENA_SIZE: usize = 1024;

#[derive(Default)]
pub struct TfliteModel {
    tensor_arena: Vec<u8>,
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
        let model_bytes_len = model_bytes.len();
        let tensor_arena_len = self.tensor_arena.len();
        let mut output_buffer_len = 0usize;
        let _ = unsafe {
            tflite_init(
                model_bytes.as_ptr(),
                model_bytes_len,
                self.tensor_arena.as_ptr(),
                tensor_arena_len,
                &mut output_buffer_len,
            )
        };
        self.output_buffer_len = Some(output_buffer_len);
        Ok(())
    }

    pub fn run(&mut self, input_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        let buffer_len = self
            .output_buffer_len
            .context("Running inference on a non-initialized TensorFlow model")?;

        let input_bytes_len = input_bytes.len();
        let mut output_bytes = vec![0; buffer_len];
        let mut output_bytes_len = 0usize;
        let _ = unsafe {
            tflite_run(
                input_bytes.as_ptr(),
                input_bytes_len,
                output_bytes.as_mut_ptr(),
                &mut output_bytes_len,
            )
        };
        if output_bytes_len <= buffer_len {
            Ok(output_bytes[..output_bytes_len].to_vec())
        } else {
            Err(anyhow!("Response size is larger than the allocated buffer"))
        }
    }
}
