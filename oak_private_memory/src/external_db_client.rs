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

use anyhow::Context;
use async_trait::async_trait;
use futures::StreamExt;
use log::info;
use prost::Message;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use sealed_memory_rust_proto::oak::private_memory::{
    DataBlob, DeleteBlobsRequest, EncryptedDataBlob, EncryptedMetadataBlob, MetadataBlob,
    ReadDataBlobRequest, ReadMetadataBlobRequest, ReadMetadataBlobResponse,
    ReadMetadataBlobStreamRequest, ReadUnencryptedDataBlobRequest, WriteDataBlobRequest,
    WriteMetadataBlobRequest, WriteMetadataBlobStreamRequest, WriteUnencryptedDataBlobRequest,
    read_metadata_blob_stream_response, write_metadata_blob_stream_request,
};
use tonic::{Code, transport::Channel};

pub type ExternalDbClient = SealedMemoryDatabaseServiceClient<Channel>;
// The unique id for a opaque blob stored in the disk.
pub type BlobId = String;

// The size of the chunks to use when streaming data to/from the external
// database. 1MB.
const CHUNK_SIZE: usize = 1024 * 1024;

// A non-fatal result from an attempt to persist the metadata db.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MetadataPersistResult {
    // The metadata db was persisted, no further action required.
    Succeeded,

    // The current metadata db is stale; fetch a new one, re-apply your changes,
    // and try persisting again.
    RetryNeeded,
}

// Handlers for storing raw data blobs in the external database.
#[async_trait]
pub trait DataBlobHandler {
    async fn add_blob(
        &mut self,
        data_blob: EncryptedDataBlob,
        id: Option<BlobId>,
    ) -> anyhow::Result<BlobId>;
    async fn add_blobs(
        &mut self,
        data_blobs: Vec<EncryptedDataBlob>,
        ids: Option<Vec<BlobId>>,
    ) -> anyhow::Result<Vec<BlobId>>;
    async fn get_blob(
        &mut self,
        id: &BlobId,
        strong_read: bool,
    ) -> anyhow::Result<Option<EncryptedDataBlob>>;
    async fn add_metadata_blob(
        &mut self,
        id: &BlobId,
        metadata_blob: EncryptedMetadataBlob,
    ) -> anyhow::Result<MetadataPersistResult>;
    async fn get_metadata_blob(
        &mut self,
        id: &BlobId,
    ) -> anyhow::Result<Option<EncryptedMetadataBlob>>;
    async fn add_metadata_blob_stream(
        &mut self,
        id: &BlobId,
        metadata_blob: EncryptedMetadataBlob,
    ) -> anyhow::Result<MetadataPersistResult>;
    async fn get_metadata_blob_stream(
        &mut self,
        id: &BlobId,
    ) -> anyhow::Result<Option<EncryptedMetadataBlob>>;
    async fn get_blobs(
        &mut self,
        ids: &[BlobId],
        strong_read: bool,
    ) -> anyhow::Result<Vec<Option<EncryptedDataBlob>>>;
    async fn add_unencrypted_blob(
        &mut self,
        data_blob: DataBlob,
        id: Option<BlobId>,
    ) -> anyhow::Result<BlobId>;
    async fn get_unencrypted_blob(
        &mut self,
        id: &BlobId,
        strong_read: bool,
    ) -> anyhow::Result<Option<DataBlob>>;

    async fn delete_blobs(&mut self, ids: &[BlobId]) -> anyhow::Result<()>;
}

#[async_trait]
impl DataBlobHandler for ExternalDbClient {
    async fn add_blob(
        &mut self,
        data_blob: EncryptedDataBlob,
        id: Option<BlobId>,
    ) -> anyhow::Result<BlobId> {
        let id = id.unwrap_or_else(|| rand::random::<u128>().to_string());
        let blob = data_blob.encode_to_vec();
        let blob_size = blob.len() as u64;
        let data_blob = DataBlob { id: id.clone(), blob };
        let start_time = tokio::time::Instant::now();
        self.write_data_blob(WriteDataBlobRequest { data_blob: Some(data_blob) }).await?;
        let mut elapsed_time = start_time.elapsed().as_millis() as u64;
        if elapsed_time == 0 {
            elapsed_time = 1;
        }
        let speed = blob_size / 1024 / elapsed_time;
        metrics::get_global_metrics().record_db_save_speed(speed);
        Ok(id)
    }

    async fn add_metadata_blob(
        &mut self,
        id: &BlobId,
        metadata_blob: EncryptedMetadataBlob,
    ) -> anyhow::Result<MetadataPersistResult> {
        let blob =
            metadata_blob.encrypted_data_blob.as_ref().context("no blob contents")?.encode_to_vec();
        let blob_size = blob.len() as u64;
        let data_blob = DataBlob { id: id.clone(), blob };
        let start_time = tokio::time::Instant::now();
        let write_result = self
            .write_metadata_blob(WriteMetadataBlobRequest {
                metadata_blob: Some(MetadataBlob {
                    data_blob: Some(data_blob),
                    version: metadata_blob.version,
                }),
            })
            .await;

        if let Err(ref status) = write_result {
            if status.code() == Code::FailedPrecondition {
                return Ok(MetadataPersistResult::RetryNeeded);
            }
            write_result?;
        }

        let mut elapsed_time = start_time.elapsed().as_millis() as u64;
        if elapsed_time == 0 {
            elapsed_time = 1;
        }
        let speed = blob_size / 1024 / elapsed_time;
        metrics::get_global_metrics().record_db_save_speed(speed);
        Ok(MetadataPersistResult::Succeeded)
    }

    async fn add_metadata_blob_stream(
        &mut self,
        id: &BlobId,
        metadata_blob: EncryptedMetadataBlob,
    ) -> anyhow::Result<MetadataPersistResult> {
        let blob =
            metadata_blob.encrypted_data_blob.as_ref().context("no blob contents")?.encode_to_vec();
        let blob_size = blob.len() as u64;

        let mut chunks = blob.chunks(CHUNK_SIZE);
        let first_chunk = chunks.next().unwrap_or_default();
        let mut messages = vec![WriteMetadataBlobStreamRequest {
            request: Some(write_metadata_blob_stream_request::Request::MetadataBlob(
                MetadataBlob {
                    data_blob: Some(DataBlob { id: id.clone(), blob: first_chunk.to_vec() }),
                    version: metadata_blob.version,
                },
            )),
        }];

        for chunk in chunks {
            messages.push(WriteMetadataBlobStreamRequest {
                request: Some(write_metadata_blob_stream_request::Request::Chunk(chunk.to_vec())),
            });
        }

        let start_time = tokio::time::Instant::now();
        let write_result = self.write_metadata_blob_stream(futures::stream::iter(messages)).await;

        if let Err(ref status) = write_result {
            if status.code() == Code::FailedPrecondition {
                return Ok(MetadataPersistResult::RetryNeeded);
            }
            write_result?;
        }

        let mut elapsed_time = start_time.elapsed().as_millis() as u64;
        if elapsed_time == 0 {
            elapsed_time = 1;
        }
        let speed = blob_size / 1024 / elapsed_time;
        metrics::get_global_metrics().record_db_save_speed(speed);
        Ok(MetadataPersistResult::Succeeded)
    }

    async fn add_blobs(
        &mut self,
        data_blobs: Vec<EncryptedDataBlob>,
        ids: Option<Vec<BlobId>>,
    ) -> anyhow::Result<Vec<BlobId>> {
        let mut result = Vec::with_capacity(data_blobs.len());
        let ids: Vec<Option<BlobId>> = if let Some(ids) = ids {
            ids.iter().map(|id| Some(id.clone())).collect()
        } else {
            vec![None; data_blobs.len()]
        };
        assert_eq!(data_blobs.len(), ids.len());
        // TOOD: b/412698203 - Ideally we should have a rpc call that does batch add.
        for (data_blob, id) in data_blobs.into_iter().zip(ids.into_iter()) {
            result.push(self.add_blob(data_blob, id).await?);
        }
        Ok(result)
    }

    async fn get_blob(
        &mut self,
        id: &BlobId,
        strong_read: bool,
    ) -> anyhow::Result<Option<EncryptedDataBlob>> {
        let start_time = tokio::time::Instant::now();
        match self.read_data_blob(ReadDataBlobRequest { id: id.clone(), strong_read }).await {
            Ok(response) => {
                let db_response = response.into_inner();
                if let Some(data_blob) = db_response.data_blob {
                    let blob_size = data_blob.blob.len() as u64;
                    let data_blob = EncryptedDataBlob::decode(&*data_blob.blob)
                        .context("Failed to decode EncryptedDataBlob")?;

                    let mut elapsed_time = start_time.elapsed().as_millis() as u64;
                    if elapsed_time == 0 {
                        elapsed_time = 1;
                    }
                    let speed = blob_size / 1024 / elapsed_time;
                    metrics::get_global_metrics().record_db_load_speed(speed);
                    return Ok(Some(data_blob));
                }
                Ok(None)
            }
            Err(status) => {
                if status.code() == Code::NotFound {
                    Ok(None)
                } else {
                    Err(status.into())
                }
            }
        }
    }

    async fn get_metadata_blob(
        &mut self,
        id: &BlobId,
    ) -> anyhow::Result<Option<EncryptedMetadataBlob>> {
        let start_time = tokio::time::Instant::now();
        match self.read_metadata_blob(ReadMetadataBlobRequest { id: id.clone() }).await {
            Ok(response) => {
                let db_response = response.into_inner();
                if let ReadMetadataBlobResponse {
                    metadata_blob: Some(MetadataBlob { data_blob: Some(data_blob), version }),
                } = db_response
                {
                    let blob_size = data_blob.blob.len() as u64;
                    let metadata_blob = EncryptedMetadataBlob {
                        encrypted_data_blob: Some(
                            EncryptedDataBlob::decode(&*data_blob.blob)
                                .context("Failed to decode EncryptedMetadataBlob")?,
                        ),
                        version,
                    };

                    let mut elapsed_time = start_time.elapsed().as_millis() as u64;
                    if elapsed_time == 0 {
                        elapsed_time = 1;
                    }
                    let speed = blob_size / 1024 / elapsed_time;
                    metrics::get_global_metrics().record_db_load_speed(speed);
                    return Ok(Some(metadata_blob));
                }
                Ok(None)
            }
            Err(status) => {
                if status.code() == Code::NotFound {
                    Ok(None)
                } else {
                    Err(status.into())
                }
            }
        }
    }

    async fn get_metadata_blob_stream(
        &mut self,
        id: &BlobId,
    ) -> anyhow::Result<Option<EncryptedMetadataBlob>> {
        let start_time = tokio::time::Instant::now();
        match self.read_metadata_blob_stream(ReadMetadataBlobStreamRequest { id: id.clone() }).await
        {
            Ok(response) => {
                let mut response_stream = response.into_inner();
                let mut full_blob = Vec::new();

                let first_response = match response_stream.next().await {
                    Some(res) => res?,
                    None => return Ok(None),
                };

                let version = match first_response.response {
                    Some(read_metadata_blob_stream_response::Response::MetadataBlob(metadata)) => {
                        if let Some(data_blob) = metadata.data_blob {
                            full_blob.extend_from_slice(&data_blob.blob);
                        }
                        metadata.version
                    }
                    _ => anyhow::bail!("Expected MetadataBlob as the first message in the stream"),
                };

                while let Some(response) = response_stream.next().await {
                    let response = response?;
                    match response.response {
                        Some(read_metadata_blob_stream_response::Response::Chunk(chunk)) => {
                            full_blob.extend_from_slice(&chunk);
                        }
                        _ => anyhow::bail!("Expected Chunk message in the stream"),
                    }
                }

                let metadata_blob = EncryptedMetadataBlob {
                    encrypted_data_blob: Some(
                        EncryptedDataBlob::decode(&*full_blob)
                            .context("Failed to decode EncryptedMetadataBlob")?,
                    ),
                    version,
                };

                let mut elapsed_time = start_time.elapsed().as_millis() as u64;
                if elapsed_time == 0 {
                    elapsed_time = 1;
                }
                let speed = full_blob.len() as u64 / 1024 / elapsed_time;
                metrics::get_global_metrics().record_db_load_speed(speed);
                Ok(Some(metadata_blob))
            }
            Err(status) => {
                if status.code() == Code::NotFound {
                    Ok(None)
                } else {
                    Err(status.into())
                }
            }
        }
    }

    async fn get_blobs(
        &mut self,
        ids: &[BlobId],
        strong_read: bool,
    ) -> anyhow::Result<Vec<Option<EncryptedDataBlob>>> {
        // TOOD: b/412698203 - Ideally we should have a rpc call that does batch get.
        let mut result = Vec::with_capacity(ids.len());
        for id in ids {
            let mut client = self.clone();
            let id = id.clone();
            result.push(tokio::spawn(async move { client.get_blob(&id, strong_read).await }));
        }
        let result = futures::future::join_all(result).await;
        result.into_iter().map(|x| x.map_err(anyhow::Error::msg)?).collect()
    }

    async fn add_unencrypted_blob(
        &mut self,
        data_blob: DataBlob,
        id: Option<BlobId>,
    ) -> anyhow::Result<BlobId> {
        let id = id.unwrap_or_else(|| data_blob.id.clone());
        // Ensure the DataBlob has the correct ID if it was generated or overridden.
        let data_blob_with_id = DataBlob { id: id.clone(), blob: data_blob.blob };
        let db_response = self
            .write_unencrypted_data_blob(WriteUnencryptedDataBlobRequest {
                data_blob: Some(data_blob_with_id),
            })
            .await
            .map_err(anyhow::Error::msg)?
            .into_inner();
        info!("db response {:#?}", db_response);
        Ok(id)
    }

    async fn get_unencrypted_blob(
        &mut self,
        id: &BlobId,
        strong_read: bool,
    ) -> anyhow::Result<Option<DataBlob>> {
        match self
            .read_unencrypted_data_blob(ReadUnencryptedDataBlobRequest {
                id: id.clone(),
                strong_read,
            })
            .await
        {
            Ok(response) => Ok(response.into_inner().data_blob),
            Err(status) => {
                if status.code() == Code::NotFound {
                    Ok(None)
                } else {
                    Err(status.into())
                }
            }
        }
    }

    async fn delete_blobs(&mut self, ids: &[BlobId]) -> anyhow::Result<()> {
        self.delete_blobs(DeleteBlobsRequest { ids: ids.to_vec() }).await?;
        Ok(())
    }
}
