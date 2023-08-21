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

use log::info;

pub mod proto {
    #![allow(dead_code)]
    use prost::Message;
    include!(concat!(env!("OUT_DIR"), "/oak.echo.rs"));
}

#[derive(Default)]
pub struct EchoService;

impl proto::Echo for EchoService {
    fn echo(
        &mut self,
        request: proto::EchoRequest,
    ) -> Result<proto::EchoResponse, micro_rpc::Status> {
        let request_body = request.body;
        info!("Received a request, size: {}", request_body.len());
        let response_body = request_body;

        Ok(proto::EchoResponse {
            body: response_body,
        })
    }
}
