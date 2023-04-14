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

#![no_std]
#![feature(never_type)]

extern crate alloc;

pub mod schema {
    #![allow(dead_code)]
    use prost::Message;
    include!(concat!(env!("OUT_DIR"), "/oak.iree.rs"));
}
mod iree;

#[derive(Default)]
pub struct IreeService {
    iree_model: iree::IreeModel,
}

impl IreeService {
    pub fn new() -> Self {
        Self {
            iree_model: iree::IreeModel::new(),
        }
    }
}

impl schema::Iree for IreeService {
    fn initialize(
        &mut self,
        _initialization: &schema::InitializeRequest,
    ) -> Result<schema::InitializeResponse, micro_rpc::Status> {
        self.iree_model
            .initialize()
            .map_err(|_err| micro_rpc::Status::new(micro_rpc::StatusCode::Internal))?;
        Ok(schema::InitializeResponse {})
    }

    fn invoke(
        &mut self,
        request_message: &schema::InvokeRequest,
    ) -> Result<schema::InvokeResponse, micro_rpc::Status> {
        let response = self
            .iree_model
            .run(&request_message.body)
            .map_err(|_err| micro_rpc::Status::new(micro_rpc::StatusCode::Internal))?;
        Ok(schema::InvokeResponse { body: response })
    }
}
