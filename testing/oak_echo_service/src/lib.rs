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

use alloc::format;

use log::info;
use oak_restricted_kernel_sdk::Attester;

pub struct EchoService<A: Attester> {
    pub attester: A,
}

impl<A> service::oak::echo::Echo for EchoService<A>
where
    A: Attester,
{
    fn echo(
        &mut self,
        request: service::oak::echo::EchoRequest,
    ) -> Result<service::oak::echo::EchoResponse, micro_rpc::Status> {
        let request_body = request.body;
        info!("Received a request, size: {}", request_body.len());
        let response_body = request_body;

        Ok(service::oak::echo::EchoResponse { body: response_body })
    }

    fn get_evidence(
        &mut self,
        _request: (),
    ) -> Result<service::oak::echo::GetEvidenceResponse, micro_rpc::Status> {
        let evidence = self.attester.quote().map_err(|err| {
            micro_rpc::Status::new_with_message(
                micro_rpc::StatusCode::Internal,
                format!("failed to get evidence: {err}"),
            )
        })?;
        Ok(service::oak::echo::GetEvidenceResponse { evidence: Some(evidence) })
    }
}
