//
// Copyright 2026 The Project Oak Authors
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

use anyhow::Context;
use encryption::{decrypt, encrypt, generate_nonce};
use external_db_client::{BlobId, DataBlobHandler};
use log::{info, warn};
use metrics::Metrics;
use oak_private_memory_database::{Database, MemoryId};
use prost::Message;
use rand::Rng;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_database_service_client::SealedMemoryDatabaseServiceClient;
use sealed_memory_rust_proto::prelude::v1::*;
use tonic::transport::Channel;
use zeroize::Zeroizing;

use crate::{
    context::UserSessionContext,
    persistence_worker::{ResourceExhaustedBackoff, ResourceExhaustedRetryPolicy},
};

pub(crate) const DEK_LENGTH_BYTES: usize = 32;

/// Memory blobs re-encrypted per `reencrypt_blobs` call.
pub(crate) const REENCRYPT_BATCH_SIZE: usize = 50;

pub(crate) fn generate_dek() -> Zeroizing<Vec<u8>> {
    let mut dek = Zeroizing::new(vec![0u8; DEK_LENGTH_BYTES]);
    rand::rng().fill(dek.as_mut_slice());
    dek
}

pub(crate) fn wrap_dek(dek: &[u8], kek: &[u8]) -> anyhow::Result<EncryptedDataBlob> {
    let nonce = generate_nonce();
    let data = encrypt(kek, &nonce, dek, b"").context("encrypting DEK with KEK")?;
    Ok(EncryptedDataBlob { nonce, data })
}

pub(crate) fn unwrap_dek(
    wrapped_dek: &EncryptedDataBlob,
    kek: &[u8],
) -> anyhow::Result<Zeroizing<Vec<u8>>> {
    let decrypted = decrypt(kek, &wrapped_dek.nonce, &wrapped_dek.data, b"")
        .context("decrypting wrapped DEK with KEK")?;
    Ok(Zeroizing::new(decrypted))
}

pub(crate) fn create_plain_text_user_info(
    key_derivation_info: Option<KeyDerivationInfo>,
    wrapped_dek: EncryptedDataBlob,
) -> PlainTextUserInfo {
    PlainTextUserInfo {
        key_derivation_info,
        wrapped_dek: Some(WrappedDataEncryptionKey { wrapped_key: Some(wrapped_dek) }),
    }
}

/// Generates a fresh DEK, wraps it under `kek`, and encodes the user's
/// `PlainTextUserInfo` into a [`DataBlob`] keyed by `uid`.
pub(crate) fn generate_wrapped_dek_blob(
    uid: &str,
    kek: &[u8],
    key_derivation_info: KeyDerivationInfo,
) -> anyhow::Result<(Zeroizing<Vec<u8>>, DataBlob)> {
    let dek = generate_dek();
    let wrapped_dek = wrap_dek(&dek, kek)?;
    let plain_text_info = create_plain_text_user_info(Some(key_derivation_info), wrapped_dek);
    let data_blob = DataBlob { id: uid.to_string(), blob: plain_text_info.encode_to_vec() };
    Ok((dek, data_blob))
}

pub(crate) fn wrapped_dek(
    plain_text_info: &PlainTextUserInfo,
) -> anyhow::Result<&EncryptedDataBlob> {
    plain_text_info
        .wrapped_dek
        .as_ref()
        .context("missing wrapped_dek")?
        .wrapped_key
        .as_ref()
        .context("missing wrapped_dek")
}

pub(crate) fn extract_and_unwrap_dek(
    plain_text_info: &PlainTextUserInfo,
    kek: &[u8],
) -> anyhow::Result<Zeroizing<Vec<u8>>> {
    unwrap_dek(wrapped_dek(plain_text_info)?, kek)
}

/// Reads the user's `PlainTextUserInfo` from storage and unwraps the DEK it
/// currently holds using the KEK.
pub(crate) async fn read_stored_dek(
    db_client: &mut SealedMemoryDatabaseServiceClient<Channel>,
    uid: &BlobId,
    kek: &[u8],
) -> anyhow::Result<Zeroizing<Vec<u8>>> {
    let user_data_blob = db_client
        .get_unencrypted_blob(uid, true)
        .await?
        .context("no PlainTextUserInfo for user")?;
    let plain_text_info = PlainTextUserInfo::decode(&*user_data_blob.blob)
        .context("failed to decode PlainTextUserInfo")?;
    extract_and_unwrap_dek(&plain_text_info, kek).context("failed to unwrap stored DEK")
}

/// Returned by [`switch_to_stored_dek`] when the stored DEK is the session's
/// DEK, so there is no rotation to switch to.
#[derive(Debug)]
pub(crate) struct DekNotRotated;

impl std::fmt::Display for DekNotRotated {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "stored DEK is the session DEK")
    }
}

impl std::error::Error for DekNotRotated {}

#[cfg(test)]
tokio::task_local! {
    /// While set for a task, [`Reencryption::undo_repoint`] fails, so tests can
    /// reach the path where a failed rotation can't restore the session.
    pub(crate) static FAIL_UNDO_REPOINT: ();
}

/// Copies of memory blobs under a new DEK that the index doesn't reference yet.
#[derive(Debug, Default)]
pub(crate) struct Reencryption {
    pub ciphertext_bytes: u64,
    /// `(memory_id, old_blob_id, new_blob_id)` for every copied blob.
    pub repoints: Vec<(MemoryId, BlobId, BlobId)>,
    /// Memories whose blob no longer exists, so there was nothing to copy.
    pub missing: Vec<(MemoryId, BlobId)>,
}

impl Reencryption {
    /// The blobs the copies replace.
    pub(crate) fn superseded(&self) -> Vec<BlobId> {
        self.repoints.iter().map(|(_, old_blob_id, _)| old_blob_id.clone()).collect()
    }

    /// Points the index and pending mutation log at the copies.
    pub(crate) fn repoint(&self, database: &mut Database) -> anyhow::Result<()> {
        database.repoint_blobs(&self.repoints)
    }

    /// Points the index and pending mutation log back at the original blobs.
    pub(crate) fn undo_repoint(&self, database: &mut Database) -> anyhow::Result<()> {
        #[cfg(test)]
        if FAIL_UNDO_REPOINT.try_with(|_| ()).is_ok() {
            anyhow::bail!("injected undo_repoint failure");
        }
        let reversed: Vec<_> = self
            .repoints
            .iter()
            .map(|(memory_id, old, new)| (memory_id.clone(), new.clone(), old.clone()))
            .collect();
        database.repoint_blobs(&reversed)
    }

    /// Soft-deletes the copies.
    pub(crate) async fn discard(&self, database: &mut Database) {
        let copies: Vec<BlobId> =
            self.repoints.iter().map(|(_, _, new_blob_id)| new_blob_id.clone()).collect();
        if !copies.is_empty()
            && let Err(e) = database.delete_blobs(&copies).await
        {
            warn!("Failed to soft-delete {} unused re-encrypted blobs: {e:?}", copies.len());
        }
    }
}

/// Copies the memory blobs in `blobs` into new blobs encrypted under `dek`, in
/// batches of [`REENCRYPT_BATCH_SIZE`], without touching the index or the
/// source blobs. `before_batch` runs before each batch, and an error from it
/// stops the copy. On any failure, the copies already written are soft-deleted.
pub(crate) async fn reencrypt_into_copies(
    database: &mut Database,
    blobs: &[(MemoryId, BlobId)],
    dek: &[u8],
    mut before_batch: impl FnMut() -> anyhow::Result<()>,
) -> anyhow::Result<Reencryption> {
    let mut reencryption = Reencryption::default();
    for chunk in blobs.chunks(REENCRYPT_BATCH_SIZE) {
        tokio::task::yield_now().await;
        let copied = match before_batch() {
            Ok(()) => {
                let blob_ids: Vec<BlobId> =
                    chunk.iter().map(|(_, blob_id)| blob_id.clone()).collect();
                database.reencrypt_blobs(&blob_ids, dek).await
            }
            Err(e) => Err(e),
        };
        let copied = match copied {
            Ok(copied) => copied,
            Err(e) => {
                reencryption.discard(database).await;
                return Err(e);
            }
        };
        reencryption.ciphertext_bytes += copied.ciphertext_bytes;
        for ((memory_id, old_blob_id), new_blob_id) in chunk.iter().zip(copied.new_blob_ids) {
            match new_blob_id {
                Some(new_blob_id) => reencryption.repoints.push((
                    memory_id.clone(),
                    old_blob_id.clone(),
                    new_blob_id,
                )),
                None => reencryption.missing.push((memory_id.clone(), old_blob_id.clone())),
            }
        }
    }
    Ok(reencryption)
}

/// Switches the session to `dek` and soft-deletes the blobs the index no longer
/// references.
pub(crate) async fn adopt_dek(
    user_context: &mut UserSessionContext,
    dek: Zeroizing<Vec<u8>>,
    superseded: &[BlobId],
) {
    user_context.dek = dek.clone();
    user_context.database.set_dek(dek);
    if !superseded.is_empty()
        && let Err(e) = user_context.database.delete_blobs(superseded).await
    {
        warn!("Failed to soft-delete {} superseded blobs: {e:?}", superseded.len());
    }
}

/// Moves a session onto a DEK another session rotated in: re-encrypts the
/// session's pending memory blobs under the stored DEK, repoints the index and
/// mutation log at the copies, and adopts the stored DEK. Fails with
/// [`DekNotRotated`] if the stored DEK is the session's DEK. On any other
/// failure the session is left as it was, unless undoing a failed repoint also
/// fails.
///
/// Reading the stored DEK, and re-encrypting the pending memories, are retried
/// while the host rejects them with `RESOURCE_EXHAUSTED`, as far as `policy`
/// allows each of them, like the persist that calls this. A re-encryption that
/// is rejected discards its copies, so it is retried from the start. (If the
/// host rejects discarding them too, they are left to expire with their TTL.)
pub(crate) async fn switch_to_stored_dek(
    user_context: &mut UserSessionContext,
    metrics: &Metrics,
    policy: ResourceExhaustedRetryPolicy,
) -> anyhow::Result<()> {
    let mut backoff = ResourceExhaustedBackoff::new(policy);
    let stored_dek = loop {
        match read_stored_dek(
            &mut user_context.database_service_client,
            &user_context.uid,
            &user_context.kek,
        )
        .await
        {
            Ok(stored_dek) => break stored_dek,
            Err(e) => backoff.wait_to_retry(e, "stored DEK read", metrics).await?,
        }
    };
    if *stored_dek == *user_context.dek {
        return Err(DekNotRotated.into());
    }
    info!("DEK rotated for user {}; switching session to the stored DEK", user_context.uid);

    let pending = user_context.database.get_pending_add_memory_blob_ids()?;
    let mut backoff = ResourceExhaustedBackoff::new(policy);
    let reencryption = loop {
        match reencrypt_into_copies(&mut user_context.database, &pending, &stored_dek, || Ok(()))
            .await
        {
            Ok(reencryption) => break reencryption,
            Err(e) => backoff
                .wait_to_retry(e, "pending memory re-encryption", metrics)
                .await
                .context("re-encrypting pending memories")?,
        }
    };
    if let Some((_, blob_id)) = reencryption.missing.first() {
        reencryption.discard(&mut user_context.database).await;
        anyhow::bail!("pending blob {blob_id} disappeared");
    }
    if let Err(e) = reencryption.repoint(&mut user_context.database) {
        reencryption.undo_repoint(&mut user_context.database).context("failed to undo repoint")?;
        reencryption.discard(&mut user_context.database).await;
        return Err(e.context("failed to repoint pending memories"));
    }
    adopt_dek(user_context, stored_dek, &reencryption.superseded()).await;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::persistence_worker::TEST_RETRY_POLICY;

    #[test]
    fn test_generate_and_wrap_unwrap_dek() {
        let kek = vec![0x42u8; 32];
        let dek = generate_dek();
        assert_eq!(dek.len(), DEK_LENGTH_BYTES);

        let wrapped = wrap_dek(&dek, &kek).expect("wrap failed");
        let unwrapped = unwrap_dek(&wrapped, &kek).expect("unwrap failed");
        assert_eq!(*dek, *unwrapped);
    }

    #[test]
    fn test_plain_text_user_info_roundtrip() {
        let kek = vec![0x42u8; 32];
        let dek = generate_dek();
        let wrapped = wrap_dek(&dek, &kek).expect("wrap failed");

        let key_derivation_info =
            KeyDerivationInfo { kek_version: 1, kek_salt: b"test_salt".to_vec() };

        let user_info = create_plain_text_user_info(Some(key_derivation_info.clone()), wrapped);
        assert_eq!(user_info.key_derivation_info, Some(key_derivation_info));

        let unwrapped = unwrap_dek(wrapped_dek(&user_info).expect("extract failed"), &kek)
            .expect("unwrap failed");
        assert_eq!(*dek, *unwrapped);
    }

    #[test]
    fn test_unwrap_with_wrong_kek_fails() {
        let kek = vec![0x42u8; 32];
        let wrong_kek = vec![0x43u8; 32];
        let dek = generate_dek();
        let wrapped = wrap_dek(&dek, &kek).expect("wrap failed");
        assert!(unwrap_dek(&wrapped, &wrong_kek).is_err());
    }

    #[test]
    fn test_wrapped_dek_missing_is_an_error() {
        let info = PlainTextUserInfo { key_derivation_info: None, wrapped_dek: None };
        assert!(wrapped_dek(&info).is_err());
    }

    const KEK: [u8; 32] = [0x42; 32];
    const UID: &str = "dek_test_user";

    fn user_info_wrapping(dek: &[u8]) -> PlainTextUserInfo {
        create_plain_text_user_info(None, wrap_dek(dek, &KEK).unwrap())
    }

    #[test]
    fn extract_and_unwrap_dek_returns_the_wrapped_dek() {
        let dek = generate_dek();

        let unwrapped = extract_and_unwrap_dek(&user_info_wrapping(&dek), &KEK).unwrap();

        assert_eq!(*unwrapped, *dek);
    }

    #[test]
    fn extract_and_unwrap_dek_without_wrapped_dek_fails() {
        let info = PlainTextUserInfo { key_derivation_info: None, wrapped_dek: None };

        assert!(extract_and_unwrap_dek(&info, &KEK).is_err());
    }

    #[test]
    fn extract_and_unwrap_dek_with_wrong_kek_fails() {
        let info = user_info_wrapping(&generate_dek());

        assert!(extract_and_unwrap_dek(&info, &[0x43; 32]).is_err());
    }

    async fn db_with_user_info(
        blob: Option<Vec<u8>>,
    ) -> SealedMemoryDatabaseServiceClient<Channel> {
        let service = std::sync::Arc::new(
            private_memory_test_database_server_lib::service::SealedMemoryDatabaseServiceTestImpl::default(),
        );
        if let Some(blob) = blob {
            service
                .unencrypted_database
                .lock()
                .await
                .insert(UID.to_string(), DataBlob { id: UID.to_string(), blob });
        }
        let db_addr = crate::test_util::start_test_db_with_service(service).await;
        SealedMemoryDatabaseServiceClient::connect(format!("http://{db_addr}")).await.unwrap()
    }

    fn error_chain(result: anyhow::Result<Zeroizing<Vec<u8>>>) -> String {
        format!("{:#}", result.expect_err("expected an error"))
    }

    #[tokio::test]
    async fn read_stored_dek_returns_the_stored_dek() {
        let dek = generate_dek();
        let mut db = db_with_user_info(Some(user_info_wrapping(&dek).encode_to_vec())).await;

        let stored = read_stored_dek(&mut db, &UID.to_string(), &KEK).await.unwrap();

        assert_eq!(*stored, *dek);
    }

    #[tokio::test]
    async fn read_stored_dek_without_user_info_fails() {
        let mut db = db_with_user_info(None).await;

        let error = error_chain(read_stored_dek(&mut db, &UID.to_string(), &KEK).await);

        assert!(error.contains("no PlainTextUserInfo for user"), "{error}");
    }

    #[tokio::test]
    async fn read_stored_dek_with_undecodable_user_info_fails() {
        let mut db = db_with_user_info(Some(vec![0xff; 8])).await;

        let error = error_chain(read_stored_dek(&mut db, &UID.to_string(), &KEK).await);

        assert!(error.contains("failed to decode PlainTextUserInfo"), "{error}");
    }

    #[tokio::test]
    async fn read_stored_dek_with_wrong_kek_fails() {
        let mut db =
            db_with_user_info(Some(user_info_wrapping(&generate_dek()).encode_to_vec())).await;

        let error = error_chain(read_stored_dek(&mut db, &UID.to_string(), &[0x43; 32]).await);

        assert!(error.contains("failed to unwrap stored DEK"), "{error}");
    }

    type TestDb = std::sync::Arc<
        private_memory_test_database_server_lib::service::SealedMemoryDatabaseServiceTestImpl,
    >;

    /// A registered, key-synced session with `count` unpersisted memories.
    async fn session_with_memories(
        count: usize,
    ) -> (
        TestDb,
        crate::handler::SealedMemorySessionHandler,
        tokio::sync::mpsc::UnboundedReceiver<UserSessionContext>,
        Vec<MemoryId>,
    ) {
        let service = TestDb::default();
        let db_addr = crate::test_util::start_test_db_with_service(service.clone()).await;
        let (handler, persistence_rx) = crate::test_util::connect_handler(db_addr);
        handler
            .user_registration_handler(crate::test_util::registration_request(UID))
            .await
            .unwrap();
        handler.key_sync_handler(crate::test_util::key_sync_request(UID, None)).await.unwrap();
        let expiration = prost_types::Timestamp { seconds: 4_102_444_800, nanos: 0 };
        let memories = (0..count)
            .map(|i| Memory {
                tags: vec![format!("memory-{i}")],
                expiration_timestamp: Some(expiration),
                ..Default::default()
            })
            .collect();
        let mut ids = Vec::with_capacity(count);
        {
            let mut guard = handler.session_context().await;
            for result in guard.as_mut().unwrap().database.add_memories(memories).await {
                ids.push(result.unwrap());
            }
        }
        (service, handler, persistence_rx, ids)
    }

    async fn stored_blob_ids(service: &TestDb) -> std::collections::BTreeSet<BlobId> {
        service.database.lock().await.keys().cloned().collect()
    }

    fn sorted<T: Ord>(mut items: Vec<T>) -> Vec<T> {
        items.sort();
        items
    }

    async fn tags_of(database: &Database, id: &MemoryId) -> Vec<String> {
        database.get_memory_by_id(id.clone(), &None).await.unwrap().unwrap().tags
    }

    #[tokio::test]
    async fn reencrypt_into_copies_copies_every_blob_under_the_new_dek() {
        let count = REENCRYPT_BATCH_SIZE + 1;
        let (service, handler, _rx, ids) = session_with_memories(count).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let blobs = ctx.database.get_all_memory_and_blob_ids().unwrap();
        let originals = service.database.lock().await.clone();
        let dek_new = generate_dek();

        let mut batches = 0;
        let reencryption = reencrypt_into_copies(&mut ctx.database, &blobs, &dek_new, || {
            batches += 1;
            Ok(())
        })
        .await
        .unwrap();

        assert_eq!(batches, 2);
        assert!(reencryption.missing.is_empty());
        assert_eq!(
            sorted(
                reencryption.repoints.iter().map(|(m, old, _)| (m.clone(), old.clone())).collect()
            ),
            sorted(blobs)
        );
        let stored = service.database.lock().await;
        for (blob_id, blob) in &originals {
            assert_eq!(stored[blob_id], *blob, "source blob {blob_id} changed");
        }
        let written: u64 =
            reencryption.repoints.iter().map(|(_, _, new)| stored[new].blob.len() as u64).sum();
        assert_eq!(reencryption.ciphertext_bytes, written);
        drop(stored);
        reencryption.repoint(&mut ctx.database).unwrap();
        ctx.database.set_dek(dek_new);
        assert_eq!(
            tags_of(&ctx.database, &ids[count - 1]).await,
            vec![format!("memory-{}", count - 1)]
        );
    }

    #[tokio::test]
    async fn reencrypt_into_copies_reports_missing_blobs() {
        let (service, handler, _rx, _) = session_with_memories(3).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let blobs = sorted(ctx.database.get_all_memory_and_blob_ids().unwrap());
        service.database.lock().await.remove(&blobs[0].1);

        let reencryption =
            reencrypt_into_copies(&mut ctx.database, &blobs, &generate_dek(), || Ok(()))
                .await
                .unwrap();

        assert_eq!(reencryption.missing, vec![blobs[0].clone()]);
        assert_eq!(
            sorted(reencryption.superseded()),
            sorted(vec![blobs[1].1.clone(), blobs[2].1.clone()])
        );
    }

    #[tokio::test]
    async fn reencrypt_into_copies_failure_discards_earlier_batches() {
        let (service, handler, _rx, _) = session_with_memories(REENCRYPT_BATCH_SIZE + 1).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let blobs = ctx.database.get_all_memory_and_blob_ids().unwrap();
        let originals = stored_blob_ids(&service).await;

        let mut batches = 0;
        let error = reencrypt_into_copies(&mut ctx.database, &blobs, &generate_dek(), || {
            batches += 1;
            if batches == 2 {
                anyhow::bail!("stop before the second batch")
            }
            Ok(())
        })
        .await
        .unwrap_err();

        assert!(format!("{error}").contains("stop before the second batch"), "{error}");
        assert_eq!(stored_blob_ids(&service).await, originals);
    }

    #[tokio::test]
    async fn reencrypt_into_copies_read_failure_discards_earlier_batches() {
        let (service, handler, _rx, _) = session_with_memories(REENCRYPT_BATCH_SIZE + 1).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let blobs = ctx.database.get_all_memory_and_blob_ids().unwrap();
        let originals = stored_blob_ids(&service).await;

        let mut batches = 0;
        let error = reencrypt_into_copies(&mut ctx.database, &blobs, &generate_dek(), || {
            batches += 1;
            if batches == 2 {
                service.fail_next_read_data_blobs.store(true, std::sync::atomic::Ordering::SeqCst);
            }
            Ok(())
        })
        .await
        .unwrap_err();

        let status = error.downcast_ref::<tonic::Status>().expect("expected a tonic::Status");
        assert_eq!(status.code(), tonic::Code::Unavailable);
        assert_eq!(stored_blob_ids(&service).await, originals);
    }

    #[tokio::test]
    async fn undo_repoint_restores_the_index_and_pending_log() {
        let (_service, handler, _rx, _) = session_with_memories(2).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let blobs = sorted(ctx.database.get_all_memory_and_blob_ids().unwrap());
        let pending = sorted(ctx.database.get_pending_add_memory_blob_ids().unwrap());
        let reencryption =
            reencrypt_into_copies(&mut ctx.database, &blobs, &generate_dek(), || Ok(()))
                .await
                .unwrap();
        let copies: Vec<(MemoryId, BlobId)> = sorted(
            reencryption.repoints.iter().map(|(m, _, new)| (m.clone(), new.clone())).collect(),
        );

        reencryption.repoint(&mut ctx.database).unwrap();
        assert_eq!(sorted(ctx.database.get_all_memory_and_blob_ids().unwrap()), copies);
        assert_eq!(sorted(ctx.database.get_pending_add_memory_blob_ids().unwrap()), copies);
        reencryption.undo_repoint(&mut ctx.database).unwrap();

        assert_eq!(sorted(ctx.database.get_all_memory_and_blob_ids().unwrap()), blobs);
        assert_eq!(sorted(ctx.database.get_pending_add_memory_blob_ids().unwrap()), pending);
    }

    #[tokio::test]
    async fn adopt_dek_switches_the_session_and_deletes_superseded_blobs() {
        let (service, handler, _rx, ids) = session_with_memories(2).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let blobs = ctx.database.get_all_memory_and_blob_ids().unwrap();
        let dek_new = generate_dek();
        let reencryption =
            reencrypt_into_copies(&mut ctx.database, &blobs, &dek_new, || Ok(())).await.unwrap();
        reencryption.repoint(&mut ctx.database).unwrap();

        adopt_dek(ctx, dek_new.clone(), &reencryption.superseded()).await;

        assert_eq!(*ctx.dek, *dek_new);
        assert_eq!(tags_of(&ctx.database, &ids[0]).await, vec!["memory-0".to_string()]);
        let stored = stored_blob_ids(&service).await;
        for blob_id in reencryption.superseded() {
            assert!(!stored.contains(&blob_id), "superseded blob {blob_id} was kept");
        }
    }

    async fn store_wrapped_dek(service: &TestDb, dek: &[u8]) {
        service.unencrypted_database.lock().await.insert(
            UID.to_string(),
            DataBlob {
                id: UID.to_string(),
                blob: create_plain_text_user_info(
                    None,
                    wrap_dek(dek, crate::test_util::TEST_KEK).unwrap(),
                )
                .encode_to_vec(),
            },
        );
    }

    #[tokio::test]
    async fn switch_to_stored_dek_without_rotation_is_dek_not_rotated() {
        let (_service, handler, _rx, _) = session_with_memories(1).await;
        let mut guard = handler.session_context().await;

        let error = switch_to_stored_dek(
            guard.as_mut().unwrap(),
            &metrics::get_global_metrics(),
            TEST_RETRY_POLICY,
        )
        .await
        .unwrap_err();

        assert!(error.is::<DekNotRotated>(), "{error:#}");
    }

    #[tokio::test]
    async fn switch_to_stored_dek_moves_pending_memories_onto_the_stored_dek() {
        let (service, handler, _rx, ids) = session_with_memories(2).await;
        let dek_new = generate_dek();
        store_wrapped_dek(&service, &dek_new).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let pending_before = ctx.database.get_pending_add_memory_blob_ids().unwrap();

        switch_to_stored_dek(ctx, &metrics::get_global_metrics(), TEST_RETRY_POLICY).await.unwrap();

        assert_eq!(*ctx.dek, *dek_new);
        let pending_after = ctx.database.get_pending_add_memory_blob_ids().unwrap();
        assert_eq!(pending_after.len(), pending_before.len());
        let stored = stored_blob_ids(&service).await;
        for (_, blob_id) in &pending_before {
            assert!(!stored.contains(blob_id), "old pending blob {blob_id} was kept");
        }
        for (id, tag) in ids.iter().zip(["memory-0", "memory-1"]) {
            assert_eq!(tags_of(&ctx.database, id).await, vec![tag.to_string()]);
        }
    }

    /// The host rejecting the stored DEK read and the pending memory reads
    /// with `RESOURCE_EXHAUSTED` delays the switch instead of failing it.
    #[tokio::test]
    async fn switch_to_stored_dek_retries_resource_exhausted_rejections() {
        let (service, handler, _rx, ids) = session_with_memories(2).await;
        let dek_new = generate_dek();
        store_wrapped_dek(&service, &dek_new).await;
        service.fail_next_unencrypted_reads(tonic::Code::ResourceExhausted, 2).await;
        service.fail_next_data_blobs_reads(tonic::Code::ResourceExhausted, 1).await;
        let harness = metrics_testing::TestMetrics::new(Metrics::new);
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();

        switch_to_stored_dek(ctx, &harness.metrics, TEST_RETRY_POLICY).await.unwrap();

        assert_eq!(*ctx.dek, *dek_new);
        assert_eq!(harness.collect().counter("db_resource_exhausted_retries", &[]), 3);
        for (id, tag) in ids.iter().zip(["memory-0", "memory-1"]) {
            assert_eq!(tags_of(&ctx.database, id).await, vec![tag.to_string()]);
        }
    }

    #[tokio::test]
    async fn switch_to_stored_dek_with_a_missing_pending_blob_leaves_the_session_unchanged() {
        let (service, handler, _rx, _) = session_with_memories(2).await;
        store_wrapped_dek(&service, &generate_dek()).await;
        let mut guard = handler.session_context().await;
        let ctx = guard.as_mut().unwrap();
        let dek_before = ctx.dek.clone();
        let pending_before = sorted(ctx.database.get_pending_add_memory_blob_ids().unwrap());
        service.database.lock().await.remove(&pending_before[0].1);
        let stored_before = stored_blob_ids(&service).await;

        let error = switch_to_stored_dek(ctx, &metrics::get_global_metrics(), TEST_RETRY_POLICY)
            .await
            .unwrap_err();

        assert!(format!("{error:#}").contains("disappeared"), "{error:#}");
        assert_eq!(*ctx.dek, *dek_before);
        assert_eq!(sorted(ctx.database.get_pending_add_memory_blob_ids().unwrap()), pending_before);
        assert_eq!(stored_blob_ids(&service).await, stored_before);
    }
}
