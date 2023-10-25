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

use crate::proto::oak::functions::{
    oak_functions_server::OakFunctions, AbortNextLookupDataResponse, Empty,
    ExtendNextLookupDataRequest, ExtendNextLookupDataResponse, FinishNextLookupDataRequest,
    FinishNextLookupDataResponse, InitializeRequest, InitializeResponse, InvokeRequest,
    InvokeResponse,
};

pub mod proto {
    pub mod oak {
        pub mod functions {
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.functions");
        }
        pub mod containers {
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.containers");
        }
        pub use oak_crypto::proto::oak::crypto;
        pub use oak_remote_attestation::proto::oak::session;
    }
}

pub mod orchestrator_client;

// Instance of the OakFunctions service for Oak Containers.
pub struct OakFunctionsContainersService {}

#[tonic::async_trait]
impl OakFunctions for OakFunctionsContainersService {
    async fn initialize(
        &self,
        request: tonic::Request<InitializeRequest>,
    ) -> Result<tonic::Response<InitializeResponse>, tonic::Status> {
        eprintln!("Received initialize request: {:?}", request);
        let response = InitializeResponse::default();
        Ok(tonic::Response::new(response))
    }

    async fn handle_user_request(
        &self,
        request: tonic::Request<InvokeRequest>,
    ) -> Result<tonic::Response<InvokeResponse>, tonic::Status> {
        eprintln!("Received invoke request: {:?}", request);
        let response = InvokeResponse::default();
        Ok(tonic::Response::new(response))
    }

    async fn extend_next_lookup_data(
        &self,
        request: tonic::Request<ExtendNextLookupDataRequest>,
    ) -> Result<tonic::Response<ExtendNextLookupDataResponse>, tonic::Status> {
        eprintln!("Received extended_next_lookup_data request: {:?}", request);
        let response = ExtendNextLookupDataResponse::default();
        Ok(tonic::Response::new(response))
    }

    async fn finish_next_lookup_data(
        &self,
        request: tonic::Request<FinishNextLookupDataRequest>,
    ) -> Result<tonic::Response<FinishNextLookupDataResponse>, tonic::Status> {
        eprintln!("Received finish_next_lookup_data request: {:?}", request);
        let response = FinishNextLookupDataResponse::default();
        Ok(tonic::Response::new(response))
    }

    async fn abort_next_lookup_data(
        &self,
        request: tonic::Request<Empty>,
    ) -> Result<tonic::Response<AbortNextLookupDataResponse>, tonic::Status> {
        eprintln!("Received abort_next_lookup_data request: {:?}", request);
        let response = AbortNextLookupDataResponse::default();
        Ok(tonic::Response::new(response))
    }
}
