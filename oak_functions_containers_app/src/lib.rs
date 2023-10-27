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

use crate::proto::oak::functions::oak_functions_server::OakFunctions;
use oak_functions_service::{
    proto::oak::functions::{
        AbortNextLookupDataResponse, Empty, ExtendNextLookupDataRequest,
        ExtendNextLookupDataResponse, FinishNextLookupDataRequest, FinishNextLookupDataResponse,
        InitializeRequest, InitializeResponse, InvokeRequest, InvokeResponse,
        OakFunctions as OakFunctionsTrait,
    },
    OakFunctionsService,
};
use oak_remote_attestation::attester::AttestationReportGenerator;
use std::sync::{Arc, Mutex};

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
pub struct OakFunctionsContainersService {
    service: Mutex<OakFunctionsService>,
}

impl OakFunctionsContainersService {
    pub fn new(attestation_report_generator: Arc<dyn AttestationReportGenerator>) -> Self {
        Self {
            service: Mutex::new(OakFunctionsService::new(attestation_report_generator)),
        }
    }
}

fn map_status(status: micro_rpc::Status) -> tonic::Status {
    let code = match status.code {
        micro_rpc::StatusCode::Ok => tonic::Code::Ok,
        micro_rpc::StatusCode::Cancelled => tonic::Code::Cancelled,
        micro_rpc::StatusCode::Unknown => tonic::Code::Unknown,
        micro_rpc::StatusCode::InvalidArgument => tonic::Code::InvalidArgument,
        micro_rpc::StatusCode::DeadlineExceeded => tonic::Code::DeadlineExceeded,
        micro_rpc::StatusCode::NotFound => tonic::Code::NotFound,
        micro_rpc::StatusCode::AlreadyExists => tonic::Code::AlreadyExists,
        micro_rpc::StatusCode::PermissionDenied => tonic::Code::PermissionDenied,
        micro_rpc::StatusCode::ResourceExhausted => tonic::Code::ResourceExhausted,
        micro_rpc::StatusCode::FailedPrecondition => tonic::Code::FailedPrecondition,
        micro_rpc::StatusCode::Aborted => tonic::Code::Aborted,
        micro_rpc::StatusCode::OutOfRange => tonic::Code::OutOfRange,
        micro_rpc::StatusCode::Unimplemented => tonic::Code::Unimplemented,
        micro_rpc::StatusCode::Internal => tonic::Code::Internal,
        micro_rpc::StatusCode::Unavailable => tonic::Code::Unavailable,
        micro_rpc::StatusCode::DataLoss => tonic::Code::DataLoss,
        micro_rpc::StatusCode::Unauthenticated => tonic::Code::Unauthenticated,
    };
    tonic::Status::new(code, status.message)
}

#[tonic::async_trait]
impl OakFunctions for OakFunctionsContainersService {
    async fn initialize(
        &self,
        request: tonic::Request<InitializeRequest>,
    ) -> Result<tonic::Response<InitializeResponse>, tonic::Status> {
        self.service
            .lock()
            .unwrap()
            .initialize(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }

    async fn handle_user_request(
        &self,
        request: tonic::Request<InvokeRequest>,
    ) -> Result<tonic::Response<InvokeResponse>, tonic::Status> {
        self.service
            .lock()
            .unwrap()
            .handle_user_request(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }

    async fn extend_next_lookup_data(
        &self,
        request: tonic::Request<ExtendNextLookupDataRequest>,
    ) -> Result<tonic::Response<ExtendNextLookupDataResponse>, tonic::Status> {
        self.service
            .lock()
            .unwrap()
            .extend_next_lookup_data(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }

    async fn finish_next_lookup_data(
        &self,
        request: tonic::Request<FinishNextLookupDataRequest>,
    ) -> Result<tonic::Response<FinishNextLookupDataResponse>, tonic::Status> {
        self.service
            .lock()
            .unwrap()
            .finish_next_lookup_data(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }

    async fn abort_next_lookup_data(
        &self,
        request: tonic::Request<Empty>,
    ) -> Result<tonic::Response<AbortNextLookupDataResponse>, tonic::Status> {
        self.service
            .lock()
            .unwrap()
            .abort_next_lookup_data(request.into_inner())
            .map(tonic::Response::new)
            .map_err(map_status)
    }
}