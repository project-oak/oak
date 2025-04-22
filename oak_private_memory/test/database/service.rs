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

use std::collections::HashMap;

use anyhow::anyhow;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_server::{
    SealedMemoryDatabaseService, SealedMemoryDatabaseServiceServer,
};
use sealed_memory_rust_proto::oak::private_memory::{
    ReadDataBlobRequest, ReadDataBlobResponse, ResetDatabaseRequest, ResetDatabaseResponse,
    WriteDataBlobRequest, WriteDataBlobResponse,
};
use tokio::net::TcpListener;
use tokio_stream::wrappers::TcpListenerStream;

#[derive(Default)]
pub struct SealedMemoryDatabaseServiceTestImpl {
    pub database: HashMap<i64, Vec<u8>>,
}

#[tonic::async_trait]
impl SealedMemoryDatabaseService for SealedMemoryDatabaseServiceTestImpl {
    async fn write_data_blob(
        &self,
        _request: tonic::Request<WriteDataBlobRequest>,
    ) -> Result<tonic::Response<WriteDataBlobResponse>, tonic::Status> {
        Ok(tonic::Response::new(WriteDataBlobResponse::default()))
    }

    async fn read_data_blob(
        &self,
        _request: tonic::Request<ReadDataBlobRequest>,
    ) -> Result<tonic::Response<ReadDataBlobResponse>, tonic::Status> {
        Ok(tonic::Response::new(ReadDataBlobResponse::default()))
    }

    async fn reset_database(
        &self,
        _request: tonic::Request<ResetDatabaseRequest>,
    ) -> Result<tonic::Response<ResetDatabaseResponse>, tonic::Status> {
        Ok(tonic::Response::new(ResetDatabaseResponse::default()))
    }
}

pub async fn create(listener: TcpListener) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(SealedMemoryDatabaseServiceServer::new(
            SealedMemoryDatabaseServiceTestImpl::default(),
        ))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
