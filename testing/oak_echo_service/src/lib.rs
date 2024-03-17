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
use oak_attestation::dice::evidence_to_proto;
use oak_restricted_kernel_sdk::attestation::EvidenceProvider;

pub mod proto {
    pub mod oak {
        pub mod attestation {
            pub mod v1 {
                pub use oak_proto_rust::oak::attestation::v1::Evidence;
            }
        }

        pub mod echo {
            #![allow(dead_code)]
            #![allow(clippy::let_unit_value)]
            use prost::Message;
            include!(concat!(env!("OUT_DIR"), "/oak.echo.rs"));
        }
    }
}

#[derive(Default)]
pub struct EchoService<EP: EvidenceProvider> {
    pub evidence_provider: EP,
}

impl<EP> proto::oak::echo::Echo for EchoService<EP>
where
    EP: EvidenceProvider,
{
    fn echo(
        &mut self,
        request: proto::oak::echo::EchoRequest,
    ) -> Result<proto::oak::echo::EchoResponse, micro_rpc::Status> {
        let request_body = request.body;
        info!("Received a request, size: {}", request_body.len());
        let response_body = request_body;

        Ok(proto::oak::echo::EchoResponse { body: response_body })
    }

    fn get_evidence(
        &mut self,
        _request: (),
    ) -> Result<proto::oak::echo::GetEvidenceResponse, micro_rpc::Status> {
        let evidence =
            evidence_to_proto(self.evidence_provider.get_evidence().clone()).map_err(|err| {
                micro_rpc::Status::new_with_message(
                    micro_rpc::StatusCode::Internal,
                    format!("failed to convert evidence to proto: {err}"),
                )
            })?;
        Ok(proto::oak::echo::GetEvidenceResponse { evidence: Some(evidence) })
    }
}
