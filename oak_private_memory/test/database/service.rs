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

use std::{
    collections::{HashMap, VecDeque},
    sync::{
        Arc,
        atomic::{AtomicBool, AtomicUsize, Ordering},
    },
    time::Duration,
};

use anyhow::anyhow;
use log::debug;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_server::{
    SealedMemoryDatabaseService, SealedMemoryDatabaseServiceServer,
};
use sealed_memory_rust_proto::oak::private_memory::{
    AcquireUnencryptedDataBlobLockRequest, AcquireUnencryptedDataBlobLockResponse, DataBlob,
    DeleteBlobsRequest, DeleteBlobsResponse, ExtendUnencryptedDataBlobLockRequest,
    ExtendUnencryptedDataBlobLockResponse, MetadataBlob, MetadataBlobNotModified,
    ReadDataBlobRequest, ReadDataBlobResponse, ReadDataBlobsRequest, ReadDataBlobsResponse,
    ReadMetadataBlobStreamRequest, ReadMetadataBlobStreamResponse, ReadUnencryptedDataBlobRequest,
    ReadUnencryptedDataBlobResponse, ReleaseUnencryptedDataBlobLockRequest,
    ReleaseUnencryptedDataBlobLockResponse, ResetDatabaseRequest, ResetDatabaseResponse,
    WriteDataBlobRequest, WriteDataBlobResponse, WriteDataBlobsRequest, WriteDataBlobsResponse,
    WriteMetadataBlobStreamRequest, WriteMetadataBlobStreamResponse,
    WriteUnencryptedDataBlobRequest, WriteUnencryptedDataBlobResponse,
    read_metadata_blob_stream_response, write_metadata_blob_stream_request,
};
use tokio::{
    net::TcpListener,
    sync::{Mutex, oneshot},
};
use tokio_stream::{StreamExt, wrappers::TcpListenerStream};

use crate::lock_state::LockError;
pub use crate::lock_state::{CLOCK_SKEW_MARGIN, LockState};

impl From<LockError> for tonic::Status {
    fn from(error: LockError) -> Self {
        match error {
            LockError::InvalidArgument(message) => tonic::Status::invalid_argument(message),
            LockError::NotFound => {
                tonic::Status::not_found("UnencryptedDataBlob row does not exist")
            }
            LockError::Conflict => tonic::Status::aborted(
                "UnencryptedDataBlob row is locked by another writer, or the lock is no longer \
                 held by the given token",
            ),
        }
    }
}

pub struct SealedMemoryDatabaseServiceTestImpl {
    pub database: Mutex<HashMap<String, DataBlob>>,
    pub metadata_database: Mutex<HashMap<String, MetadataBlob>>,
    pub unencrypted_database: Mutex<HashMap<String, DataBlob>>,
    pub held_unencrypted_write: Mutex<Option<HeldWrite>>,
    pub held_metadata_write: Mutex<Option<HeldWrite>>,
    /// Statuses that the next streamed metadata blob writes fail with, in
    /// order. See [`Self::fail_next_metadata_writes`].
    pub metadata_write_failures: Mutex<VecDeque<tonic::Status>>,
    /// Statuses that the next streamed metadata blob reads fail with, in
    /// order. See [`Self::fail_next_metadata_reads`].
    pub metadata_read_failures: Mutex<VecDeque<tonic::Status>>,
    /// Number of streamed metadata blob writes received, including failed
    /// ones.
    pub metadata_write_calls: AtomicUsize,
    /// The blob of every streamed metadata blob write received, including
    /// failed ones, in order.
    pub metadata_write_payloads: Mutex<Vec<Vec<u8>>>,
    /// Number of streamed metadata blob reads received, including failed ones.
    pub metadata_read_calls: AtomicUsize,
    /// When true, `ReadMetadataBlobStream` ignores `known_version` and always
    /// sends the blob.
    pub ignore_known_version: AtomicBool,
    /// When set, the next `ReadMetadataBlobStream` replies with exactly these
    /// messages, e.g. to send a malformed stream.
    pub next_metadata_stream_reply: Mutex<Option<Vec<ReadMetadataBlobStreamResponse>>>,
    /// When true, metadata blob writes omit `committed_version` (e.g. when the
    /// host could not read back the committed version).
    pub omit_committed_version: AtomicBool,
    /// The `known_version` of every `ReadMetadataBlobStream` request.
    pub metadata_stream_known_versions: Mutex<Vec<String>>,
    /// Number of `ReadMetadataBlobStream` replies that sent the blob.
    pub metadata_blob_downloads: AtomicUsize,
    /// Number of `ReadMetadataBlobStream` replies that were `not_modified`.
    pub metadata_not_modified_replies: AtomicUsize,
    /// Number of metadata blob writes rejected for a version conflict.
    pub metadata_write_conflicts: AtomicUsize,
    pub lock_state: Arc<LockState>,
}

pub struct HeldWrite {
    arrived: oneshot::Sender<()>,
    release: oneshot::Receiver<()>,
}

impl Default for SealedMemoryDatabaseServiceTestImpl {
    fn default() -> Self {
        Self {
            database: Mutex::new(HashMap::new()),
            metadata_database: Mutex::new(HashMap::new()),
            unencrypted_database: Mutex::new(HashMap::new()),
            held_unencrypted_write: Mutex::new(None),
            held_metadata_write: Mutex::new(None),
            metadata_write_failures: Mutex::new(VecDeque::new()),
            metadata_read_failures: Mutex::new(VecDeque::new()),
            metadata_write_calls: AtomicUsize::new(0),
            metadata_write_payloads: Mutex::new(Vec::new()),
            metadata_read_calls: AtomicUsize::new(0),
            ignore_known_version: AtomicBool::new(false),
            next_metadata_stream_reply: Mutex::new(None),
            omit_committed_version: AtomicBool::new(false),
            metadata_stream_known_versions: Mutex::new(Vec::new()),
            metadata_blob_downloads: AtomicUsize::new(0),
            metadata_not_modified_replies: AtomicUsize::new(0),
            metadata_write_conflicts: AtomicUsize::new(0),
            lock_state: LockState::new(),
        }
    }
}

impl SealedMemoryDatabaseServiceTestImpl {
    pub async fn hold_next_unencrypted_write(
        &self,
    ) -> (oneshot::Receiver<()>, oneshot::Sender<()>) {
        let (arrived_tx, arrived_rx) = oneshot::channel();
        let (release_tx, release_rx) = oneshot::channel();
        *self.held_unencrypted_write.lock().await =
            Some(HeldWrite { arrived: arrived_tx, release: release_rx });
        (arrived_rx, release_tx)
    }

    /// Makes the next streamed metadata blob write block once it has been
    /// received, until the returned sender is used (or dropped). The returned
    /// receiver fires when the held write arrives.
    pub async fn hold_next_metadata_write(&self) -> (oneshot::Receiver<()>, oneshot::Sender<()>) {
        let (arrived_tx, arrived_rx) = oneshot::channel();
        let (release_tx, release_rx) = oneshot::channel();
        *self.held_metadata_write.lock().await =
            Some(HeldWrite { arrived: arrived_tx, release: release_rx });
        (arrived_rx, release_tx)
    }

    /// Makes the next `count` streamed metadata blob writes fail with `code`
    /// without storing anything, like the real host does when it rejects a
    /// call under memory pressure (`RESOURCE_EXHAUSTED`).
    pub async fn fail_next_metadata_writes(&self, code: tonic::Code, count: usize) {
        self.metadata_write_failures
            .lock()
            .await
            .extend((0..count).map(|_| tonic::Status::new(code, "injected write failure")));
    }

    /// Makes the next `count` streamed metadata blob reads fail with `code`
    /// before reading anything, like the real host does when it rejects a
    /// call under memory pressure (`RESOURCE_EXHAUSTED`).
    pub async fn fail_next_metadata_reads(&self, code: tonic::Code, count: usize) {
        self.metadata_read_failures
            .lock()
            .await
            .extend((0..count).map(|_| tonic::Status::new(code, "injected read failure")));
    }

    pub async fn add_blob_inner(&self, id: String, blob: DataBlob) {
        self.database.lock().await.insert(id, blob);
    }
    /// Writes `blob` if its version matches the stored one (or nothing is
    /// stored), and returns the newly committed version. Returns `None` on a
    /// version conflict.
    pub async fn add_metadata_blob_inner(
        &self,
        id: String,
        mut blob: MetadataBlob,
    ) -> Option<String> {
        let mut db = self.metadata_database.lock().await;

        // Check if the provided version matches the currently stored version.
        if let Some(existing_blob) = db.get(id.as_str())
            && existing_blob.version != blob.version
        {
            self.metadata_write_conflicts.fetch_add(1, Ordering::SeqCst);
            return None;
        }

        // Trivial versioning mechanism: just append a 1 for each version increment.
        blob.version = format!("{}1", blob.version);
        let committed_version = blob.version.clone();
        db.insert(id, blob);
        Some(committed_version)
    }

    /// The `committed_version` to report for a write that committed
    /// `version`.
    fn reported_committed_version(&self, version: String) -> String {
        if self.omit_committed_version.load(Ordering::SeqCst) { String::new() } else { version }
    }
    pub async fn get_blob_inner(&self, id: &str) -> Option<DataBlob> {
        self.database.lock().await.get(id).cloned()
    }
    pub async fn get_metdata_blob_inner(&self, id: &str) -> Option<MetadataBlob> {
        self.metadata_database.lock().await.get(id).cloned()
    }

    async fn row_exists(&self, id: &str) -> bool {
        self.unencrypted_database.lock().await.contains_key(id)
            || self.metadata_database.lock().await.contains_key(id)
    }

    async fn lock_conflict(&self, id: &str, lock_token: &str) -> Option<tonic::Status> {
        let row_exists = self.row_exists(id).await;
        if self.lock_state.rejects_write(id, lock_token, row_exists).await {
            Some(tonic::Status::aborted(format!(
                "UnencryptedDataBlob row {id} is locked by another writer"
            )))
        } else {
            None
        }
    }
}

#[tonic::async_trait]
impl SealedMemoryDatabaseService for SealedMemoryDatabaseServiceTestImpl {
    async fn write_data_blob(
        &self,
        request: tonic::Request<WriteDataBlobRequest>,
    ) -> Result<tonic::Response<WriteDataBlobResponse>, tonic::Status> {
        tokio::time::sleep(Duration::from_millis(150)).await;
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
        tokio::time::sleep(Duration::from_millis(150)).await;
        let request = request.into_inner();
        let blob = self.get_blob_inner(&request.id).await;
        debug!("Read {:?}, blob {:?}", request, blob);

        if let Some(blob) = blob {
            Ok(tonic::Response::new(ReadDataBlobResponse { data_blob: Some(blob) }))
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
        self.metadata_write_calls.fetch_add(1, Ordering::SeqCst);
        let mut stream = request.into_inner();
        let first = stream
            .next()
            .await
            .ok_or_else(|| tonic::Status::invalid_argument("empty WriteMetadataBlobStream"))??;
        let lock_token = first.lock_token;
        let unencrypted_data_blob = first.unencrypted_data_blob;
        let Some(write_metadata_blob_stream_request::Request::MetadataBlob(metadata)) =
            first.request
        else {
            return Err(tonic::Status::invalid_argument("first message must be a metadata blob"));
        };
        let version = metadata.version;
        let DataBlob { id, blob: mut full_blob } = metadata.data_blob.unwrap_or_default();
        while let Some(request) = stream.next().await {
            let Some(write_metadata_blob_stream_request::Request::Chunk(chunk)) = request?.request
            else {
                return Err(tonic::Status::invalid_argument("subsequent messages must be chunks"));
            };
            full_blob.extend_from_slice(&chunk);
        }
        self.metadata_write_payloads.lock().await.push(full_blob.clone());
        if let Some(status) = self.metadata_write_failures.lock().await.pop_front() {
            return Err(status);
        }

        check_unencrypted_blob_id(unencrypted_data_blob.as_ref(), &id)?;

        let held = self.held_metadata_write.lock().await.take();
        if let Some(HeldWrite { arrived, release }) = held {
            let _ = arrived.send(());
            let _ = release.await;
        }

        // Like the host, check the lock at commit time, so a lock taken while
        // this write was in flight is still detected.
        if let Some(status) = self.lock_conflict(&id, &lock_token).await {
            return Err(status);
        }

        let committed_version = self
            .add_metadata_blob_inner(
                id.clone(),
                MetadataBlob { data_blob: Some(DataBlob { id, blob: full_blob }), version },
            )
            .await;
        let Some(version) = committed_version else {
            return Ok(tonic::Response::new(WriteMetadataBlobStreamResponse {
                version_conflict: true,
                ..Default::default()
            }));
        };
        if let Some(unencrypted) = unencrypted_data_blob {
            self.unencrypted_database.lock().await.insert(unencrypted.id.clone(), unencrypted);
        }
        Ok(tonic::Response::new(WriteMetadataBlobStreamResponse {
            version_conflict: false,
            committed_version: self.reported_committed_version(version),
        }))
    }

    async fn read_metadata_blob_stream(
        &self,
        request: tonic::Request<ReadMetadataBlobStreamRequest>,
    ) -> Result<tonic::Response<Self::ReadMetadataBlobStreamStream>, tonic::Status> {
        self.metadata_read_calls.fetch_add(1, Ordering::SeqCst);
        if let Some(status) = self.metadata_read_failures.lock().await.pop_front() {
            return Err(status);
        }
        let request = request.into_inner();
        self.metadata_stream_known_versions.lock().await.push(request.known_version.clone());
        let reply = |messages: Vec<ReadMetadataBlobStreamResponse>| {
            let stream: Self::ReadMetadataBlobStreamStream =
                Box::pin(tokio_stream::iter(messages.into_iter().map(Ok)));
            Ok(tonic::Response::new(stream))
        };
        if let Some(messages) = self.next_metadata_stream_reply.lock().await.take() {
            return reply(messages);
        }
        let Some(blob) = self.get_metdata_blob_inner(&request.id).await else {
            return Err(tonic::Status::not_found("Blob not found"));
        };

        let response = if !request.known_version.is_empty()
            && request.known_version == blob.version
            && !self.ignore_known_version.load(Ordering::SeqCst)
        {
            self.metadata_not_modified_replies.fetch_add(1, Ordering::SeqCst);
            read_metadata_blob_stream_response::Response::NotModified(MetadataBlobNotModified {})
        } else {
            self.metadata_blob_downloads.fetch_add(1, Ordering::SeqCst);
            read_metadata_blob_stream_response::Response::MetadataBlob(blob)
        };
        reply(vec![ReadMetadataBlobStreamResponse { response: Some(response) }])
    }

    async fn write_unencrypted_data_blob(
        &self,
        request: tonic::Request<WriteUnencryptedDataBlobRequest>,
    ) -> Result<tonic::Response<WriteUnencryptedDataBlobResponse>, tonic::Status> {
        let request = request.into_inner();
        let data_blob = request.data_blob.expect("data_blob should be present");
        let held = self.held_unencrypted_write.lock().await.take();
        if let Some(HeldWrite { arrived, release }) = held {
            let _ = arrived.send(());
            let _ = release.await;
        }
        if let Some(status) = self.lock_conflict(&data_blob.id, &request.lock_token).await {
            return Err(status);
        }
        let mut unencrypted_db = self.unencrypted_database.lock().await;
        // Without a lock token, WriteUnencryptedDataBlob only inserts new rows
        // and rejects existing ones.
        if request.lock_token.is_empty()
            && (unencrypted_db.contains_key(&data_blob.id)
                || self.metadata_database.lock().await.contains_key(&data_blob.id))
        {
            return Err(tonic::Status::already_exists(format!(
                "UnencryptedDataBlob row {} already exists",
                data_blob.id
            )));
        }
        // The `encrypted_blob` field in DataBlob is used for unencrypted data here.
        unencrypted_db.insert(data_blob.id.clone(), data_blob);
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
        self.metadata_database.lock().await.clear();
        self.unencrypted_database.lock().await.clear();
        self.lock_state.clear().await;
        Ok(tonic::Response::new(ResetDatabaseResponse {}))
    }

    async fn delete_blobs(
        &self,
        request: tonic::Request<DeleteBlobsRequest>,
    ) -> Result<tonic::Response<DeleteBlobsResponse>, tonic::Status> {
        let request = request.into_inner();
        let mut db = self.database.lock().await;
        for id in request.ids {
            if db.remove(&id).is_none() {
                return Err(tonic::Status::not_found(format!("Blob {} not found", id)));
            }
        }
        Ok(tonic::Response::new(DeleteBlobsResponse {}))
    }

    async fn read_data_blobs(
        &self,
        request: tonic::Request<ReadDataBlobsRequest>,
    ) -> Result<tonic::Response<ReadDataBlobsResponse>, tonic::Status> {
        let request = request.into_inner();
        let db = self.database.lock().await;
        let mut data_blobs = std::collections::HashMap::new();
        for id in request.ids {
            if let Some(blob) = db.get(&id) {
                data_blobs.insert(id, blob.clone());
            }
        }
        Ok(tonic::Response::new(ReadDataBlobsResponse {
            data_blobs,
            failed_ids: Default::default(),
        }))
    }

    async fn write_data_blobs(
        &self,
        request: tonic::Request<WriteDataBlobsRequest>,
    ) -> Result<tonic::Response<WriteDataBlobsResponse>, tonic::Status> {
        let request = request.into_inner();
        let mut db = self.database.lock().await;
        for data_blob in request.data_blobs {
            db.insert(data_blob.id.clone(), data_blob);
        }
        Ok(tonic::Response::new(WriteDataBlobsResponse { failed_ids: Default::default() }))
    }

    async fn acquire_unencrypted_data_blob_lock(
        &self,
        request: tonic::Request<AcquireUnencryptedDataBlobLockRequest>,
    ) -> Result<tonic::Response<AcquireUnencryptedDataBlobLockResponse>, tonic::Status> {
        let request = request.into_inner();
        let duration = LockState::lease_duration(request.lock_duration)?;
        let row_exists = self.row_exists(&request.id).await;
        let (lock_token, expires_at) =
            self.lock_state.acquire(&request.id, duration, row_exists).await?;
        Ok(tonic::Response::new(AcquireUnencryptedDataBlobLockResponse {
            lock_token,
            lock_expire_time: Some(expires_at.into()),
        }))
    }

    async fn extend_unencrypted_data_blob_lock(
        &self,
        request: tonic::Request<ExtendUnencryptedDataBlobLockRequest>,
    ) -> Result<tonic::Response<ExtendUnencryptedDataBlobLockResponse>, tonic::Status> {
        let request = request.into_inner();
        let duration = LockState::lease_duration(request.lock_duration)?;
        let row_exists = self.row_exists(&request.id).await;
        let expires_at =
            self.lock_state.extend(&request.id, &request.lock_token, duration, row_exists).await?;
        Ok(tonic::Response::new(ExtendUnencryptedDataBlobLockResponse {
            lock_expire_time: Some(expires_at.into()),
        }))
    }

    async fn release_unencrypted_data_blob_lock(
        &self,
        request: tonic::Request<ReleaseUnencryptedDataBlobLockRequest>,
    ) -> Result<tonic::Response<ReleaseUnencryptedDataBlobLockResponse>, tonic::Status> {
        let request = request.into_inner();
        let row_exists = self.row_exists(&request.id).await;
        self.lock_state.release(&request.id, &request.lock_token, row_exists).await?;
        Ok(tonic::Response::new(ReleaseUnencryptedDataBlobLockResponse {}))
    }
}

fn check_unencrypted_blob_id(
    unencrypted_data_blob: Option<&DataBlob>,
    metadata_id: &str,
) -> Result<(), tonic::Status> {
    match unencrypted_data_blob {
        Some(unencrypted) if unencrypted.id != metadata_id => {
            Err(tonic::Status::invalid_argument(format!(
                "unencrypted_data_blob id {} does not match metadata blob id {metadata_id}",
                unencrypted.id
            )))
        }
        _ => Ok(()),
    }
}

pub async fn create(listener: TcpListener) -> Result<(), anyhow::Error> {
    create_with_lock_state(listener, LockState::new()).await
}

pub async fn create_with_lock_state(
    listener: TcpListener,
    lock_state: Arc<LockState>,
) -> Result<(), anyhow::Error> {
    serve(
        listener,
        Arc::new(SealedMemoryDatabaseServiceTestImpl { lock_state, ..Default::default() }),
    )
    .await
}

pub async fn serve(
    listener: TcpListener,
    service: Arc<SealedMemoryDatabaseServiceTestImpl>,
) -> Result<(), anyhow::Error> {
    tonic::transport::Server::builder()
        .add_service(SealedMemoryDatabaseServiceServer::from_arc(service))
        .serve_with_incoming(TcpListenerStream::new(listener))
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
