//
// Copyright 2025 The Project Oak Authors
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

use std::collections::BTreeMap;

use anyhow::Result;
use oak_attestation_types::assertion_generator::AssertionGenerator;
use oak_grpc::oak::verity::oak_verity_service_server::OakVerityService as OakVerityServiceTrait;
use oak_proto_rust::oak::verity::{ExecuteRequest, ExecuteResponse};
use oak_verity::OakVerity;
use tonic::{Request, Response, Status};

/// Wrapper around the core [`OakVerity`] library to expose it as a gRPC
/// service.
pub struct OakVerityService {
    oak_verity: OakVerity,
}

impl OakVerityService {
    pub fn new(assertion_generators: BTreeMap<String, Box<dyn AssertionGenerator>>) -> Self {
        let oak_verity = OakVerity { assertion_generators };
        Self { oak_verity }
    }
}

#[tonic::async_trait]
impl OakVerityServiceTrait for OakVerityService {
    async fn execute(
        &self,
        request: Request<ExecuteRequest>,
    ) -> Result<Response<ExecuteResponse>, Status> {
        let request = request.into_inner();
        let response = self
            .oak_verity
            .execute(request)
            .map_err(|err| Status::internal(format!("failed to execute wasm module: {}", err)))?;
        Ok(Response::new(response))
    }
}
