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
#![feature(never_type)]

extern crate alloc;

pub mod schema {
    #![allow(dead_code)]
    use prost::Message;
    include!(concat!(env!("OUT_DIR"), "/oak.tensorflow.rs"));
}
mod tflite;

#[derive(Default)]
pub struct TensorflowService {
    tflite_model: tflite::TfliteModel,
}

impl TensorflowService {
    pub fn new() -> Self {
        Self {
            tflite_model: tflite::TfliteModel::new(),
        }
    }
}

impl schema::Tensorflow for TensorflowService {
    fn initialize(
        &mut self,
        initialization: &schema::InitializeRequest,
    ) -> Result<schema::InitializeResponse, oak_idl::Status> {
        self.tflite_model
            .initialize(&initialization.tensorflow_model)
            .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;
        Ok(schema::InitializeResponse {})
    }

    fn invoke(
        &mut self,
        request_message: &schema::InvokeRequest,
    ) -> Result<schema::InvokeResponse, oak_idl::Status> {
        let response = self
            .tflite_model
            .run(&request_message.body)
            .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?;
        Ok(schema::InvokeResponse { body: response })
    }
}
