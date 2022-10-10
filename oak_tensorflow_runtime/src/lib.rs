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
    #![allow(
        clippy::derivable_impls,
        clippy::extra_unused_lifetimes,
        clippy::needless_borrow,
        dead_code,
        unused_imports
    )]

    include!(concat!(env!("OUT_DIR"), "/schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/schema_services_servers.rs"));
}

#[derive(Default)]
pub struct RuntimeImplementation {}

impl RuntimeImplementation {
    pub fn new() -> Self {
        Self {}
    }
}

impl schema::TensorflowRuntime for RuntimeImplementation {
    fn initialize(
        &mut self,
        _initialization: &schema::InitializeRequest,
    ) -> Result<oak_idl::utils::OwnedFlatbuffer<crate::schema::InitializeResponse>, oak_idl::Status>
    {
        let response_message = {
            let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
            let initialize_response = schema::InitializeResponse::create(
                &mut builder,
                &schema::InitializeResponseArgs {},
            );
            builder
                .finish(initialize_response)
                .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?
        };
        Ok(response_message)
    }

    fn invoke(
        &mut self,
        _request_message: &schema::InvokeRequest,
    ) -> Result<oak_idl::utils::OwnedFlatbuffer<schema::InvokeResponse>, oak_idl::Status> {
        let response_message = {
            let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
            let body = builder.create_vector::<u8>(&[]);
            let invoke_response = schema::InvokeResponse::create(
                &mut builder,
                &schema::InvokeResponseArgs { body: Some(body) },
            );
            builder
                .finish(invoke_response)
                .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?
        };
        Ok(response_message)
    }
}
