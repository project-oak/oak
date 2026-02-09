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
use log::debug;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_server::{
    SealedMemoryDatabaseService, SealedMemoryDatabaseServiceServer,
};
use sealed_memory_rust_proto::oak::private_memory::{
    DataBlob, DeleteBlobsRequest, DeleteBlobsResponse, MetadataBlob, ReadDataBlobRequest,
    ReadDataBlobResponse, ReadMetadataBlobRequest, ReadMetadataBlobResponse,
    ReadMetadataBlobStreamRequest, ReadMetadataBlobStreamResponse, ReadUnencryptedDataBlobRequest,
    ReadUnencryptedDataBlobResponse, ResetDatabaseRequest, ResetDatabaseResponse,
    WriteDataBlobRequest, WriteDataBlobResponse, WriteMetadataBlobRequest,
    WriteMetadataBlobResponse, WriteMetadataBlobStreamRequest, WriteMetadataBlobStreamResponse,
    WriteUnencryptedDataBlobRequest, WriteUnencryptedDataBlobResponse,
    read_metadata_blob_stream_response, write_metadata_blob_stream_request,
};
use tokio::{net::TcpListener, sync::Mutex};
use tokio_stream::{StreamExt, wrappers::TcpListenerStream};

pub struct SealedMemoryDatabaseServiceTestImpl {
    pub database: Mutex<HashMap<String, DataBlob>>,
    pub metadata_database: Mutex<HashMap<String, MetadataBlob>>,
    pub unencrypted_database: Mutex<HashMap<String, DataBlob>>,
}

impl Default for SealedMemoryDatabaseServiceTestImpl {
    fn default() -> Self {
        Self {
            database: Mutex::new(HashMap::new()),
            metadata_database: Mutex::new(HashMap::new()),
            unencrypted_database: Mutex::new(HashMap::new()),
        }
    }
}

impl SealedMemoryDatabaseServiceTestImpl {
    pub async fn add_blob_inner(&self, id: String, blob: DataBlob) {
        self.database.lock().await.insert(id, blob);
    }
    pub async fn add_metadata_blob_inner(&self, id: String, mut blob: MetadataBlob) -> bool {
        let mut db = self.metadata_database.lock().await;

        // Check if the provided version matches the currently stored version.
        if let Some(existing_blob) = db.get(id.as_str()) {
            if existing_blob.version != blob.version {
                return false;
            }
        }

        // Trivial versioning mechanism: just append a 1 for each version increment.
        blob.version = format!("{}1", blob.version);
        db.insert(id, blob);
        true
    }
    pub async fn get_blob_inner(&self, id: &str) -> Option<DataBlob> {
        self.database.lock().await.get(id).cloned()
    }
    pub async fn get_metdata_blob_inner(&self, id: &str) -> Option<MetadataBlob> {
        self.metadata_database.lock().await.get(id).cloned()
    }
}

#[tonic::async_trait]
impl SealedMemoryDatabaseService for SealedMemoryDatabaseServiceTestImpl {
    async fn write_data_blob(
        &self,
        request: tonic::Request<WriteDataBlobRequest>,
    ) -> Result<tonic::Response<WriteDataBlobResponse>, tonic::Status> {
        let request = request.into_inner();
        self.add_blob_inner(
            request.data_blob.as_ref().unwrap().id.clone(),
            request.data_blob.unwrap(),
        )
        .await;
        Ok(tonic::Response::new(WriteDataBlobResponse {}))
    }

    async fn read_data_blob(
        &self,
        request: tonic::Request<ReadDataBlobRequest>,
    ) -> Result<tonic::Response<ReadDataBlobResponse>, tonic::Status> {
        let request = request.into_inner();
        let blob = self.get_blob_inner(&request.id).await;
        debug!("Read {:?}, blob {:?}", request, blob);

        if let Some(blob) = blob {
            Ok(tonic::Response::new(ReadDataBlobResponse { data_blob: Some(blob) }))
        } else {
            Err(tonic::Status::not_found("Blob not found"))
        }
    }

    async fn write_metadata_blob(
        &self,
        request: tonic::Request<WriteMetadataBlobRequest>,
    ) -> Result<tonic::Response<WriteMetadataBlobResponse>, tonic::Status> {
        // TODO: b/443329966 - implement a fake opportunistic concurrency check here,
        // matching the expected semantics (returning a failure if the provided version
        // does not match the existing stored one)
        let request = request.into_inner();
        let added = self
            .add_metadata_blob_inner(
                request.metadata_blob.as_ref().unwrap().data_blob.as_ref().unwrap().id.clone(),
                request.metadata_blob.unwrap(),
            )
            .await;
        if !added {
            // "failed precondition" is a signal to the caller to re-fetch and try again.
            Err(tonic::Status::failed_precondition("metadata blob version mismatch"))
        } else {
            Ok(tonic::Response::new(WriteMetadataBlobResponse {}))
        }
    }

    async fn read_metadata_blob(
        &self,
        request: tonic::Request<ReadMetadataBlobRequest>,
    ) -> Result<tonic::Response<ReadMetadataBlobResponse>, tonic::Status> {
        let request = request.into_inner();
        let blob = self.get_metdata_blob_inner(&request.id).await;
        debug!("Read {:?}, blob {:?}", request, blob);

        if let Some(blob) = blob {
            Ok(tonic::Response::new(ReadMetadataBlobResponse { metadata_blob: Some(blob) }))
        } else {
            Err(tonic::Status::not_found("Blob not found"))
        }
    }

    type ReadMetadataBlobStreamStream = std::pin::Pin<
        Box<
            dyn tokio_stream::Stream<Item = Result<ReadMetadataBlobStreamResponse, tonic::Status>>
                + Send,
        >,
    >;

    async fn write_metadata_blob_stream(
        &self,
        request: tonic::Request<tonic::Streaming<WriteMetadataBlobStreamRequest>>,
    ) -> Result<tonic::Response<WriteMetadataBlobStreamResponse>, tonic::Status> {
        let mut stream = request.into_inner();
        let mut full_blob = Vec::new();
        let mut version = String::new();
        let mut id = String::new();

        while let Some(request) = stream.next().await {
            let request = request?;
            match request.request {
                Some(write_metadata_blob_stream_request::Request::MetadataBlob(metadata)) => {
                    version = metadata.version;
                    if let Some(data_blob) = metadata.data_blob {
                        id = data_blob.id;
                        full_blob.extend_from_slice(&data_blob.blob);
                    }
                }
                Some(write_metadata_blob_stream_request::Request::Chunk(chunk)) => {
                    full_blob.extend_from_slice(&chunk);
                }
                None => {}
            }
        }

        let added = self
            .add_metadata_blob_inner(
                id.clone(),
                MetadataBlob { data_blob: Some(DataBlob { id, blob: full_blob }), version },
            )
            .await;
        if !added {
            Err(tonic::Status::failed_precondition("metadata blob version mismatch"))
        } else {
            Ok(tonic::Response::new(WriteMetadataBlobStreamResponse {}))
        }
    }

    async fn read_metadata_blob_stream(
        &self,
        request: tonic::Request<ReadMetadataBlobStreamRequest>,
    ) -> Result<tonic::Response<Self::ReadMetadataBlobStreamStream>, tonic::Status> {
        let request = request.into_inner();
        let blob = self.get_metdata_blob_inner(&request.id).await;

        if let Some(blob) = blob {
            let response = ReadMetadataBlobStreamResponse {
                response: Some(read_metadata_blob_stream_response::Response::MetadataBlob(blob)),
            };
            let stream = tokio_stream::iter(vec![Ok(response)]);
            Ok(tonic::Response::new(Box::pin(stream)))
        } else {
            Err(tonic::Status::not_found("Blob not found"))
        }
    }

    async fn write_unencrypted_data_blob(
        &self,
        request: tonic::Request<WriteUnencryptedDataBlobRequest>,
    ) -> Result<tonic::Response<WriteUnencryptedDataBlobResponse>, tonic::Status> {
        let request = request.into_inner();
        // The `encrypted_blob` field in DataBlob is used for unencrypted data here.
        self.unencrypted_database.lock().await.insert(
            request.data_blob.as_ref().expect("data_blob should be present").id.clone(),
            request.data_blob.unwrap(),
        );
        Ok(tonic::Response::new(WriteUnencryptedDataBlobResponse {}))
    }

    async fn read_unencrypted_data_blob(
        &self,
        request: tonic::Request<ReadUnencryptedDataBlobRequest>,
    ) -> Result<tonic::Response<ReadUnencryptedDataBlobResponse>, tonic::Status> {
        let request = request.into_inner();
        let blob = self.unencrypted_database.lock().await.get(&request.id).cloned();
        if let Some(blob) = blob {
            Ok(tonic::Response::new(ReadUnencryptedDataBlobResponse { data_blob: Some(blob) }))
        } else {
            Err(tonic::Status::not_found("Blob not found"))
        }
    }

    async fn reset_database(
        &self,
        _request: tonic::Request<ResetDatabaseRequest>,
    ) -> Result<tonic::Response<ResetDatabaseResponse>, tonic::Status> {
        self.database.lock().await.clear();
        self.unencrypted_database.lock().await.clear();
        Ok(tonic::Response::new(ResetDatabaseResponse {}))
    }

    async fn delete_blobs(
        &self,
        request: tonic::Request<DeleteBlobsRequest>,
    ) -> Result<tonic::Response<DeleteBlobsResponse>, tonic::Status> {
        let request = request.into_inner();
        let mut db = self.database.lock().await;
        for id in request.ids {
            db.remove(&id);
        }
        Ok(tonic::Response::new(DeleteBlobsResponse {}))
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
