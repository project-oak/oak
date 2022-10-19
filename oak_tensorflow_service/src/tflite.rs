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
use anyhow::anyhow;

// TODO(#3297): Decide the TensorFlow model format to be passed as `model_bytes`.
#[link(name = "tflite-micro", kind = "static")]
extern "C" {
    /// Initializes the TensorFlow model and returns a corresponding error code.
    ///
    /// Memory area that will be used by the TFLM memory manager is defined by `tensor_arena_bytes`:
    /// <https://github.com/tensorflow/tflite-micro/blob/main/tensorflow/lite/micro/docs/memory_management.md>
    fn tflite_init(
        model_bytes: *const u8,
        model_bytes_len: u64,
        tensor_arena_bytes: *const u8,
        tensor_arena_bytes_len: u64,
    ) -> i32;

    /// Performs inference on `input_bytes` and pass inference result to `output_bytes` and returns
    /// an error code.
    /// `output_bytes` are allocated and freed by TensorFlow Lite.
    fn tflite_run(
        input_bytes: *const u8,
        input_bytes_len: u64,
        output_bytes: *mut *const u8,
        output_bytes_len: *mut u64,
    ) -> i32;
}

// TODO(#3297): Use 8GiB or 10GiB arena sizes.
const TENSOR_ARENA_SIZE: usize = 1024;

#[derive(Default)]
pub struct TfliteModel {
    tensor_arena: Vec<u8>,
}

impl TfliteModel {
    pub fn new() -> Self {
        let tensor_arena = vec![0; TENSOR_ARENA_SIZE];
        Self { tensor_arena }
    }

    pub fn initialize(&self, model_bytes: &[u8]) -> anyhow::Result<()> {
        let model_bytes_len = model_bytes
            .len()
            .try_into()
            .map_err(|error| anyhow!("Failed to convert model bytes length to u64: {}", error))?;
        let tensor_arena_len =
            self.tensor_arena.len().try_into().map_err(|error| {
                anyhow!("Failed to convert tensor arena length to u64: {}", error)
            })?;
        let _ = unsafe {
            tflite_init(
                model_bytes.as_ptr(),
                model_bytes_len,
                self.tensor_arena.as_ptr(),
                tensor_arena_len,
            )
        };
        Ok(())
    }

    pub fn run(&self, input_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        let input_bytes_len = input_bytes
            .len()
            .try_into()
            .map_err(|error| anyhow!("Failed to convert input bytes length to u64: {}", error))?;

        // TensorFlow Lite is the owner of the corresponding `output_bytes` buffer.
        let output_bytes_ptr: *mut *const u8 = &mut core::ptr::null();
        let mut output_bytes_len_ptr = 0u64;

        let _ = unsafe {
            tflite_run(
                input_bytes.as_ptr(),
                input_bytes_len,
                output_bytes_ptr,
                &mut output_bytes_len_ptr as *mut u64,
            )
        };

        let output_bytes_len = output_bytes_len_ptr
            .try_into()
            .map_err(|error| anyhow!("Failed to get output bytes length from bytes: {}", error))?;

        let output_bytes =
            unsafe { alloc::slice::from_raw_parts(*output_bytes_ptr, output_bytes_len) };
        Ok(output_bytes.to_vec())
    }
}
