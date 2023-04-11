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

#[link(name = "iree", kind = "static")]
extern "C" {
    /// Initializes the IREE model and returns a corresponding error code.
    ///
    /// This function returns a buffer size value in the `expected_output_len_ptr`. This buffer
    /// should be allocated before calling `iree_run` to store inference results.
    fn iree_init(expected_output_len_ptr: *mut usize) -> i32;

    /// Performs inference on `input_bytes_ptr` and pass inference result to `output_bytes_ptr` and
    /// returns an error code.
    ///
    /// The value in the `output_bytes_len_ptr` cannot be bigger than the value in
    /// `output_buffer_len_ptr` from `iree_init`.
    fn iree_run(
        input_bytes_ptr: *const u8,
        input_bytes_len: usize,
        output_bytes_ptr: *mut u8,
        output_bytes_len_ptr: *mut usize,
    ) -> i32;

    /// Cleans up IREE resources.
    fn iree_cleanup() -> c_void;
}

pub struct IreeModel {
    /// Defines a output buffer length that should be preallocated before calling `iree_run`.
    /// This value is only initialized after `initialize` function because IREE should return the
    /// `output_buffer_len`.
    /// If the value is `None` then `IreeModel` hasn't been initialized yet.
    output_buffer_len: Option<usize>,
}

impl Default for IreeModel {
    fn default() -> Self {
        Self::new()
    }
}

impl IreeModel {
    pub fn new() -> Self {
        Self {
            output_buffer_len: None,
        }
    }

    pub fn initialize(&mut self) -> anyhow::Result<()> {
        log!(Level::Info, "Initializing the IREE model");
        let mut expected_output_len = 0usize;
        let result_code = unsafe { iree_init(&mut expected_output_len) };
        if result_code == 0 {
            self.output_buffer_len = Some(expected_output_len);
            log!(Level::Info, "IREE model has been successfully initialized");
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
                panic!(
                    "output bytes length of {} is bigger than the output buffer length of {}",
                    output_bytes_len, output_buffer_len
                );
            }
        } else {
            log!(
                Level::Error,
                "couldn't run IREE inference, code: {}",
                result_code
            );
            Err(anyhow!(
                "couldn't run IREE inference, code: {}",
                result_code
            ))
        }
    }
}

impl Drop for IreeModel {
    fn drop(&mut self) {
        unsafe {
            iree_cleanup();
        }
    }
}
