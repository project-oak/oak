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
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/schema_services_servers.rs"));
}

pub struct RuntimeImplementation {}

impl RuntimeImplementation {
    pub fn new() -> Self {
        Self {}
    }
}

impl schema::TrustedRuntime for RuntimeImplementation {
    fn echo(
        &mut self,
        request_message: &schema::EchoRequest,
    ) -> Result<oak_idl::utils::OwnedFlatbuffer<schema::EchoResponse>, oak_idl::Status> {
        let request_body: &[u8] = request_message
                    .body()
                    .ok_or_else(|| oak_idl::Status::new(oak_idl::StatusCode::InvalidArgument))?;
        let response_body = request_body;

        let response_message = {
            let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
            let body = builder.create_vector::<u8>(&response_body);
            let user_request_response = schema::EchoResponse::create(
                &mut builder,
                &schema::EchoResponseArgs { body: Some(body) },
            );
            builder
                .finish(user_request_response)
                .map_err(|_err| oak_idl::Status::new(oak_idl::StatusCode::Internal))?
        };
        Ok(response_message)
    }
}
