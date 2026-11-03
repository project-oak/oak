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
use prost_types::Timestamp;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use sealed_memory_rust_proto::oak::private_memory::{
    DataBlob, DeleteBlobsRequest, EncryptedDataBlob, EncryptedMetadataBlob, MetadataBlob,
    ReadDataBlobRequest, ReadDataBlobsRequest, ReadMetadataBlobStreamRequest,
    ReadUnencryptedDataBlobRequest, WriteDataBlobRequest, WriteDataBlobsRequest,
    WriteMetadataBlobStreamRequest, WriteUnencryptedDataBlobRequest,
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MetadataPersistResult {
    // The metadata db was persisted, no further action required.
    //
    // `committed_version` is the version the write committed, or `None` when
    // nothing was written (or if the host could not determine it).
    Succeeded { committed_version: Option<String> },

    // The current metadata db is stale; fetch a new one, re-apply your changes,
    // and try persisting again.
    RetryNeeded,
}

impl MetadataPersistResult {
    /// A successful write whose committed version is `committed_version`, as
    /// reported by the host (empty if not reported).
    fn succeeded(committed_version: String) -> Self {
        let committed_version = (!committed_version.is_empty()).then_some(committed_version);
        Self::Succeeded { committed_version }
    }
}

// The result of reading the metadata blob with `get_metadata_blob_stream`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MetadataBlobRead {
    // The stored metadata blob.
    Blob(EncryptedMetadataBlob),

    // The stored metadata blob still has the caller's known version, so it
    // wasn't sent.
    NotModified,

    // There is no metadata blob.
    NotFound,
}

// Handlers for storing raw data blobs in the external database.
#[async_trait]
pub trait DataBlobHandler {
    async fn add_blob(
        &mut self,
        data_blob: EncryptedDataBlob,
        id: Option<BlobId>,
        coarsened_expiration_timestamp: Timestamp,
    ) -> anyhow::Result<BlobId>;

    async fn get_blob(&mut self, id: &BlobId) -> anyhow::Result<Option<EncryptedDataBlob>>;
    /// Fails with the host's `tonic::Status` itself as the error (not wrapped
    /// in context), so that callers can retry host rejections such as
    /// `RESOURCE_EXHAUSTED`.
    async fn add_metadata_blob_stream(
        &mut self,
        id: &BlobId,
        metadata_blob: &EncryptedMetadataBlob,
        coarsened_expiration_timestamp: Timestamp,
    ) -> anyhow::Result<MetadataPersistResult>;
    /// Reads the metadata blob `id`.
    ///
    /// If `known_version` is set (and not empty), the host skips sending the
    /// blob when its stored version is still `known_version`, and this returns
    /// [`MetadataBlobRead::NotModified`].
    ///
    /// Fails with the host's `tonic::Status` itself as the error (not wrapped
    /// in context), so that callers can retry host rejections such as
    /// `RESOURCE_EXHAUSTED`.
    async fn get_metadata_blob_stream(
        &mut self,
        id: &BlobId,
        coarsened_expiration_timestamp: Timestamp,
        known_version: Option<&str>,
    ) -> anyhow::Result<MetadataBlobRead>;
    async fn get_blobs(&mut self, ids: &[BlobId])
    -> anyhow::Result<Vec<Option<EncryptedDataBlob>>>;
    async fn add_blobs(
        &mut self,
        data_blobs: Vec<DataBlob>,
        coarsened_expiration_timestamp: Timestamp,
    ) -> anyhow::Result<()>;
    /// Insert a new unencrypted data blob row for `id` (or `data_blob.id` if
    /// `id` is `None`). Fails with `ALREADY_EXISTS` if the row already exists.
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
        coarsened_expiration_timestamp: Timestamp,
    ) -> anyhow::Result<BlobId> {
        let id = id.unwrap_or_else(|| rand::random::<u128>().to_string());
        let blob = data_blob.encode_to_vec();
        let data_blob = DataBlob { id: id.clone(), blob };
        self.write_data_blob(WriteDataBlobRequest {
            data_blob: Some(data_blob),
            coarsened_expiration_timestamp: Some(coarsened_expiration_timestamp),
        })
        .await?;
        Ok(id)
    }

    async fn add_metadata_blob_stream(
        &mut self,
        id: &BlobId,
        metadata_blob: &EncryptedMetadataBlob,
        coarsened_expiration_timestamp: Timestamp,
    ) -> anyhow::Result<MetadataPersistResult> {
        let blob =
            metadata_blob.encrypted_data_blob.as_ref().context("no blob contents")?.encode_to_vec();

        let mut chunks = blob.chunks(CHUNK_SIZE);
        let first_chunk = chunks.next().unwrap_or_default();
        let mut messages = vec![WriteMetadataBlobStreamRequest {
            request: Some(write_metadata_blob_stream_request::Request::MetadataBlob(
                MetadataBlob {
                    data_blob: Some(DataBlob { id: id.clone(), blob: first_chunk.to_vec() }),
                    version: metadata_blob.version.clone(),
                },
            )),
            coarsened_expiration_timestamp: Some(coarsened_expiration_timestamp),
            lock_token: String::new(),
            unencrypted_data_blob: None,
        }];

        for chunk in chunks {
            messages.push(WriteMetadataBlobStreamRequest {
                request: Some(write_metadata_blob_stream_request::Request::Chunk(chunk.to_vec())),
                coarsened_expiration_timestamp: None,
                lock_token: String::new(),
                unencrypted_data_blob: None,
            });
        }

        let write_result = self.write_metadata_blob_stream(futures::stream::iter(messages)).await;

        match write_result {
            Ok(response) => {
                let response = response.into_inner();
                if response.version_conflict {
                    return Ok(MetadataPersistResult::RetryNeeded);
                }
                Ok(MetadataPersistResult::succeeded(response.committed_version))
            }
            Err(ref status) if status.code() == Code::FailedPrecondition => {
                // Backwards compatibility: old host returns FAILED_PRECONDITION
                // as an RPC error. Remove this branch once host is updated.
                Ok(MetadataPersistResult::RetryNeeded)
            }
            Err(status) => Err(status.into()),
        }
    }

    async fn get_blob(&mut self, id: &BlobId) -> anyhow::Result<Option<EncryptedDataBlob>> {
        match self.read_data_blob(ReadDataBlobRequest { id: id.clone() }).await {
            Ok(response) => {
                let db_response = response.into_inner();
                if let Some(data_blob) = db_response.data_blob {
                    let data_blob = EncryptedDataBlob::decode(&*data_blob.blob)
                        .context("decoding EncryptedDataBlob")?;
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

    async fn get_metadata_blob_stream(
        &mut self,
        id: &BlobId,
        coarsened_expiration_timestamp: Timestamp,
        known_version: Option<&str>,
    ) -> anyhow::Result<MetadataBlobRead> {
        let known_version = known_version.unwrap_or_default();
        let response = self
            .read_metadata_blob_stream(ReadMetadataBlobStreamRequest {
                id: id.clone(),
                coarsened_expiration_timestamp: Some(coarsened_expiration_timestamp),
                known_version: known_version.to_string(),
            })
            .await;
        let mut response_stream = match response {
            Ok(response) => response.into_inner(),
            Err(status) if status.code() == Code::NotFound => {
                return Ok(MetadataBlobRead::NotFound);
            }
            Err(status) => return Err(status.into()),
        };

        let first_response = match response_stream.next().await {
            Some(res) => res?,
            None => return Ok(MetadataBlobRead::NotFound),
        };

        let mut full_blob = Vec::new();
        let version = match first_response.response {
            Some(read_metadata_blob_stream_response::Response::MetadataBlob(metadata)) => {
                if let Some(data_blob) = metadata.data_blob {
                    full_blob.extend_from_slice(&data_blob.blob);
                }
                metadata.version
            }
            Some(read_metadata_blob_stream_response::Response::NotModified(_)) => {
                if known_version.is_empty() {
                    anyhow::bail!("Got not_modified without a known version");
                }
                if let Some(next) = response_stream.next().await {
                    next?;
                    anyhow::bail!("Expected no messages after not_modified in the stream");
                }
                return Ok(MetadataBlobRead::NotModified);
            }
            _ => anyhow::bail!(
                "Expected MetadataBlob or NotModified as the first message in the stream"
            ),
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
                EncryptedDataBlob::decode(&*full_blob).context("decoding EncryptedMetadataBlob")?,
            ),
            version,
        };
        Ok(MetadataBlobRead::Blob(metadata_blob))
    }

    async fn get_blobs(
        &mut self,
        ids: &[BlobId],
    ) -> anyhow::Result<Vec<Option<EncryptedDataBlob>>> {
        let response =
            self.read_data_blobs(ReadDataBlobsRequest { ids: ids.to_vec() }).await?.into_inner();
        ids.iter()
            .map(|id| match response.data_blobs.get(id) {
                Some(data_blob) => {
                    let encrypted = EncryptedDataBlob::decode(&*data_blob.blob)
                        .context("decoding EncryptedDataBlob")?;
                    Ok(Some(encrypted))
                }
                None => Ok(None),
            })
            .collect()
    }

    async fn add_blobs(
        &mut self,
        data_blobs: Vec<DataBlob>,
        coarsened_expiration_timestamp: Timestamp,
    ) -> anyhow::Result<()> {
        let response = self
            .write_data_blobs(WriteDataBlobsRequest {
                data_blobs,
                coarsened_expiration_timestamp: Some(coarsened_expiration_timestamp),
            })
            .await?
            .into_inner();
        if !response.failed_ids.is_empty() {
            let failed_keys: Vec<&String> = response.failed_ids.keys().collect();
            anyhow::bail!("WriteDataBlobs failed for IDs: {:?}", failed_keys);
        }
        Ok(())
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
                lock_token: String::new(),
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
