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

//! This file contains all of the logic for calculating an recording metrics
/// in the Private Memory server application.
///
/// When adding new metrics, try to create clear, easy-to-use API additions, so
/// that the usage site needs just a line or two of code to correctly record the
/// metrics.
use std::sync::{Arc, Mutex, PoisonError};

use lazy_static::lazy_static;
use oak_containers_agent::metrics::OakObserver;
use opentelemetry::{
    KeyValue, Value,
    metrics::{Counter, Gauge, Histogram, Meter},
};
use prost::Name;
use sealed_memory_rust_proto::prelude::v1::*;

pub struct Metrics {
    // Total number of RPCs received by the private memory server.
    rpc_count: Counter<u64>,
    // Number of RPCs that failed.
    rpc_failure_count: Counter<u64>,
    // Latency of handling each application request.
    rpc_latency: Histogram<u64>,
    // Size of the encrypted database in bytes, on key sync load and persist.
    db_size: Histogram<u64>,
    // Latency of Icing database initialization.
    db_init_latency: Histogram<u64>,
    // Latency of expired memories cleanup.
    db_cleanup_latency: Histogram<u64>,
    // Number of expired memories cleaned up during a cleanup.
    db_cleanup_count: Histogram<u64>,
    // Latency of persisting the database.
    db_persist_latency: Histogram<u64>,
    // Latency of persisting the database, including retries.
    db_persist_latency_with_retries: Histogram<u64>,
    // Number of attempts to successfully persist the database.
    db_persist_attempts: Histogram<u64>,
    // Number of retries when connecting to the database.
    db_connect_retries: Counter<u64>,
    // Number of failures when persisting the database.
    db_persist_failures: Counter<u64>,
    // Number of database calls retried because the host rejected them with
    // RESOURCE_EXHAUSTED (host memory pressure).
    db_resource_exhausted_retries: Counter<u64>,
    // Number of persist attempts rejected with ABORTED due to a held row lock.
    db_persist_lock_conflict_count: Counter<u64>,
    // Time a persist spent waiting for a held row lock.
    db_persist_lock_wait_latency: Histogram<u64>,
    // Number of failures when syncing keys.
    decrypt_dek_failures: Counter<u64>,
    // Number of failures when deserializing user info.
    user_info_deserialization_failures: Counter<u64>,
    // Number of failures when decrypting database.
    db_decryption_failures: Counter<u64>,
    // Queue size of the in the database persist queue.
    db_persist_queue_size: Gauge<u64>,
    // The number of sessions in the database persist queue, as last recorded
    // in `db_persist_queue_size`. Updated and recorded under the lock, so
    // that concurrent updates can't record out of order.
    db_persist_queue_count: Mutex<u64>,
    // Optimize latency.
    db_optimize_latency: Histogram<u64>,
    // Speed of saving the database (KB/ms).
    db_save_speed: Histogram<u64>,
    // Speed of loading the database (KB/ms).
    db_load_speed: Histogram<u64>,
    // Latency of fetching the metadata blob from external DB during key sync.
    key_sync_db_fetch_latency: Histogram<u64>,
    // Latency of decrypting the database during key sync.
    key_sync_decrypt_latency: Histogram<u64>,
    // Number of operations that failed to replay during a database rebase.
    db_rebase_operation_failures: Counter<u64>,
    // Number of failures when cleaning expired memories.
    db_cleanup_failures: Counter<u64>,
    // Number of TLS handshake failures.
    tls_handshake_failures: Counter<u64>,
    // Number of TLS data receive errors.
    tls_receive_failures: Counter<u64>,
    // Number of failures when enqueueing a session for persistence.
    persistence_enqueue_failures: Counter<u64>,
    // Number of blobs that should have been soft-deleted but were not
    // (due to flush failures after persist).
    orphaned_blob_deletes: Counter<u64>,
    // Number of sessions rejected due to low memory.
    session_rejected_low_memory: Counter<u64>,
    // Number of sessions rejected by admission control, labelled by `reason`
    // (see [`SessionRejectReason`]).
    session_rejected: Counter<u64>,
    // Number of currently live sessions (each may own an Icing instance).
    active_sessions: Gauge<u64>,
    // Configured cap on live sessions (`max_active_sessions`).
    max_active_sessions: Gauge<u64>,
    // Number of memory mappings of the process (lines in /proc/self/maps).
    process_map_count: Gauge<u64>,

    // Icing initialization stats
    icing_init_status: Counter<u64>,
    icing_init_latency_ms: Histogram<u64>,

    // Recovery stats (labelled by component)
    icing_recovery_cause: Counter<u64>,
    icing_recovery_latency_ms: Histogram<u64>,

    // Failure counting distributions
    icing_num_previous_init_failures: Histogram<u64>,
    icing_num_failed_reindexed_documents: Histogram<u64>,

    // Number of database syncs that skipped downloading the database because
    // its stored version hadn't changed.
    db_pull_skipped_count: Counter<u64>,

    // DEK rotation.
    dek_rotation_count: Counter<u64>,
    dek_rotation_blobs_reencrypted_total: Counter<u64>,
    dek_rotation_bytes_reencrypted_total: Counter<u64>,
    dek_rotation_lock_extend_failures: Counter<u64>,
    dek_rotation_blobs_per_run: Histogram<u64>,
    dek_rotation_bytes_per_run: Histogram<u64>,
    dek_rotation_throughput_bytes_per_sec: Histogram<u64>,
    dek_rotation_latency_ms: Histogram<u64>,
}

/// The possible metrics request types.
/// This enum is private, it's wrapped by the public [`RequestMetricName`] type
/// which exposes constructors for creating types in a specific way.
#[derive(Clone, Debug)]
enum RequestMetricNameInner {
    SealedMemoryRequest(String),
    Handshake,
    Total,
    DecryptionFailure,
    DeserializationFailure,
    EmptyTlsFrame,
    EmptyRequest,
    SessionStart,
}

#[derive(Clone, Debug)]
pub struct RequestMetricName(RequestMetricNameInner);

/// Bytes in a binary kilobyte (KiB).
const KB: usize = 1_024;
/// Bytes in a binary megabyte (MiB).
const MB: usize = 1_024 * KB;

/// Why admission control rejected a new session. Used as the `reason` column
/// of the `session_rejected` counter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SessionRejectReason {
    /// Live sessions reached `max_active_sessions`.
    MaxSessions,
    /// Available RAM is below `min_available_memory_ratio`.
    LowMemory,
    /// The process map count reached `max_map_count_ratio` of
    /// `vm.max_map_count`.
    MapCount,
}

impl SessionRejectReason {
    pub const ALL: [SessionRejectReason; 3] = [
        SessionRejectReason::MaxSessions,
        SessionRejectReason::LowMemory,
        SessionRejectReason::MapCount,
    ];

    pub fn as_str(&self) -> &'static str {
        match self {
            SessionRejectReason::MaxSessions => "max_sessions",
            SessionRejectReason::LowMemory => "low_memory",
            SessionRejectReason::MapCount => "map_count",
        }
    }
}

// Explicit bucket boundaries for the `db_size` histogram, in bytes.
//
// Without these, OpenTelemetry uses its default boundaries, whose largest
// finite bucket is 10,000. Databases are tens of MB, so every sample would
// otherwise land in the overflow bucket, making the recorded distribution
// unusable. See the OpenTelemetry spec for the default boundaries:
// https://opentelemetry.io/docs/specs/otel/metrics/sdk/#explicit-bucket-histogram-aggregation
//
// Values are multiples of `MB` (binary megabytes), the same unit
// `bucket_db_size` uses.
const DB_SIZE_BYTES_BOUNDARIES: &[f64] = &[
    0.,
    MB as f64,
    (5 * MB) as f64,
    (10 * MB) as f64,
    (20 * MB) as f64,
    (30 * MB) as f64,
    (40 * MB) as f64,
    (50 * MB) as f64,
    (75 * MB) as f64,
    (100 * MB) as f64,
    (150 * MB) as f64,
    (200 * MB) as f64,
    (300 * MB) as f64,
    (400 * MB) as f64,
    (500 * MB) as f64,
];

// The following histograms previously relied on OpenTelemetry's default bucket
// boundaries, whose largest finite bucket is 10,000. Each constant below keeps
// those default boundaries and just adds more, so existing buckets keep their
// meaning while the extended range becomes visible. See the spec:
// https://opentelemetry.io/docs/specs/otel/metrics/sdk/#explicit-bucket-histogram-aggregation

/// Millisecond-latency boundaries: the OpenTelemetry defaults plus a slow tail
/// extended to 2 minutes, so latencies beyond 10 s no longer fall into
/// overflow.
const LATENCY_MS_BOUNDARIES: &[f64] = &[
    // OpenTelemetry defaults.
    0., 5., 10., 25., 50., 75., 100., 250., 500., 750., 1_000., 2_500., 5_000., 7_500., 10_000.,
    // Added slow tail.
    20_000., 30_000., 60_000., 120_000.,
];

/// Count boundaries: the OpenTelemetry defaults plus finer low-end buckets for
/// the small counts these histograms usually record.
const COUNT_BOUNDARIES: &[f64] = &[
    // Added low-end resolution.
    0., 1., 2., 3., //
    // OpenTelemetry defaults.
    5., 10., 25., 50., 75., 100., 250., 500., 750., 1_000., 2_500., 5_000., 7_500., 10_000.,
];

/// Transfer-speed boundaries in KB/ms (equivalently MB/s): the OpenTelemetry
/// defaults plus finer low-end buckets for slow transfers.
const SPEED_KB_PER_MS_BOUNDARIES: &[f64] = &[
    // Added low-end resolution.
    0., 1., 2., 3., //
    // OpenTelemetry defaults.
    5., 10., 25., 50., 75., 100., 250., 500., 750., 1_000., 2_500., 5_000., 7_500., 10_000.,
];

/// `response_type` label for `dek_rotation_count`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DekRotationResponseType {
    Ok,
    /// A retryable failure (`ABORTED`, `UNAVAILABLE`, `DEADLINE_EXCEEDED` or
    /// `RESOURCE_EXHAUSTED`).
    RetryError,
    /// The session can't rotate yet: `UNAUTHENTICATED`, or
    /// `FAILED_PRECONDITION`, e.g. because KeySync hasn't run.
    Unauthenticated,
    InternalError,
    InvalidArgument,
}

impl DekRotationResponseType {
    pub const ALL: [DekRotationResponseType; 5] = [
        DekRotationResponseType::Ok,
        DekRotationResponseType::RetryError,
        DekRotationResponseType::Unauthenticated,
        DekRotationResponseType::InternalError,
        DekRotationResponseType::InvalidArgument,
    ];

    pub fn as_str(&self) -> &'static str {
        match self {
            DekRotationResponseType::Ok => "ok",
            DekRotationResponseType::RetryError => "retry_error",
            DekRotationResponseType::Unauthenticated => "unauthenticated",
            DekRotationResponseType::InternalError => "internal_error",
            DekRotationResponseType::InvalidArgument => "invalid_argument",
        }
    }
}

/// Byte-rate boundaries in bytes/s (64 KiB/s to 1 GiB/s in powers of 4).
const BYTES_PER_SEC_BOUNDARIES: &[f64] = &[
    0.,
    (64 * KB) as f64,
    (256 * KB) as f64,
    MB as f64,
    (4 * MB) as f64,
    (16 * MB) as f64,
    (64 * MB) as f64,
    (256 * MB) as f64,
    (1_024 * MB) as f64,
];

impl Metrics {
    pub fn new(meter: &Meter) -> Self {
        let rpc_count = meter
            .u64_counter("rpc_count")
            .with_description("Total number of RPCs received by the private memory server.")
            .build();
        let rpc_failure_count = meter
            .u64_counter("rpc_failure_count")
            .with_description("Number of RPCs that failed.")
            .build();
        let rpc_latency = meter
            .u64_histogram("rpc_latency")
            .with_description(
                "Latency in ms of handling each application request, excluding the handshake, \
                 decryption and encryption.",
            )
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();
        let db_size = meter
            .u64_histogram("db_size")
            .with_description(
                "Size in bytes of the encrypted database, recorded when key sync loads it and \
                 each time it is persisted.",
            )
            .with_unit("By")
            .with_boundaries(DB_SIZE_BYTES_BOUNDARIES.to_vec())
            .build();
        let db_init_latency = meter
            .u64_histogram("db_init_latency")
            .with_description("Latency of Icing database initialization.")
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();
        let db_cleanup_latency = meter
            .u64_histogram("db_cleanup_latency")
            .with_description("Latency of expired memories cleanup operation.")
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();
        let db_cleanup_count = meter
            .u64_histogram("db_cleanup_count")
            .with_description("Number of expired memories cleaned up during cleanup operation.")
            .with_boundaries(COUNT_BOUNDARIES.to_vec())
            .build();
        let db_persist_latency = meter
            .u64_histogram("db_persist_latency")
            .with_description("Latency of persisting the database.")
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();
        let db_persist_latency_with_retries = meter
            .u64_histogram("db_persist_latency_with_retries")
            .with_description("Latency of persisting the database including all retry attempts.")
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();
        let db_persist_attempts = meter
            .u64_histogram("db_persist_attempts")
            .with_description("Number of attempts before metadata persist succeeds.")
            .with_boundaries(COUNT_BOUNDARIES.to_vec())
            .build();
        let db_connect_retries = meter
            .u64_counter("db_connect_retries")
            .with_description("Number of retries when connecting to the database.")
            .build();

        let db_persist_failures = meter
            .u64_counter("db_persist_failures")
            .with_description("Number of failures when persisting the database.")
            .build();

        let db_decryption_failures = meter
            .u64_counter("db_decryption_failures")
            .with_description("Number of failures when decrypting the database.")
            .build();

        let db_persist_queue_size = meter
            .u64_gauge("db_persist_queue_size")
            .with_description("Number of items in the database persist queue.")
            .build();

        let decrypt_dek_failures = meter
            .u64_counter("decrypt_dek_failures")
            .with_description("Number of failures when decrypting the DEK.")
            .build();

        let user_info_deserialization_failures = meter
            .u64_counter("user_info_deserialization_failures")
            .with_description("Number of failures when deserializing user info.")
            .build();

        let db_optimize_latency = meter
            .u64_histogram("db_optimize_latency")
            .with_description("Latency of optimizing the database.")
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();
        let db_save_speed = meter
            .u64_histogram("db_save_speed")
            .with_description("Speed of saving the database.")
            .with_unit("KB/ms")
            .with_boundaries(SPEED_KB_PER_MS_BOUNDARIES.to_vec())
            .build();
        let db_load_speed = meter
            .u64_histogram("db_load_speed")
            .with_description("Speed of loading the database.")
            .with_unit("KB/ms")
            .with_boundaries(SPEED_KB_PER_MS_BOUNDARIES.to_vec())
            .build();
        let key_sync_db_fetch_latency = meter
            .u64_histogram("key_sync_db_fetch_latency")
            .with_description("Latency of fetching metadata blob from external DB.")
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();
        let key_sync_decrypt_latency = meter
            .u64_histogram("key_sync_decrypt_latency")
            .with_description("Latency of decrypting the database.")
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();

        let db_rebase_operation_failures = meter
            .u64_counter("db_rebase_operation_failures")
            .with_description("Number of operations that failed to replay during DB rebase.")
            .build();

        let db_cleanup_failures = meter
            .u64_counter("db_cleanup_failures")
            .with_description("Number of failures when cleaning expired memories.")
            .build();

        let tls_handshake_failures = meter
            .u64_counter("tls_handshake_failures")
            .with_description("Number of TLS handshake failures.")
            .build();

        let tls_receive_failures = meter
            .u64_counter("tls_receive_failures")
            .with_description("Number of TLS data receive errors.")
            .build();

        let persistence_enqueue_failures = meter
            .u64_counter("persistence_enqueue_failures")
            .with_description("Number of failures enqueueing sessions for persistence.")
            .build();

        // Admission-control metrics. Keep these ahead of the icing_* instruments:
        // the host OTel->streamz bridge drops every instrument after the first one
        // that fails to export, so earlier instruments are more robust.
        let session_rejected_low_memory = meter
            .u64_counter("session_rejected_low_memory")
            .with_description("Number of sessions rejected due to low memory.")
            .build();
        let session_rejected = meter
            .u64_counter("session_rejected")
            .with_description("Number of new sessions rejected by admission control, by reason.")
            .build();
        let active_sessions = meter
            .u64_gauge("active_sessions")
            .with_description("Number of currently live sessions (each may own an Icing instance).")
            .build();
        let max_active_sessions = meter
            .u64_gauge("max_active_sessions")
            .with_description("Configured cap on live sessions per enclave.")
            .build();
        let process_map_count = meter
            .u64_gauge("process_map_count")
            .with_description(
                "Number of memory mappings of the process (lines in /proc/self/maps).",
            )
            .build();

        // Initialize the total count to 0 to trigger the metric registration.
        // Otherwise, the metric will only show up once it has been incremented.
        rpc_count.add(0, &[KeyValue::new("request_type", "total")]);
        rpc_count.add(0, &[KeyValue::new("request_type", RequestMetricName::session_start())]);
        // Likewise, register a failure series for every request type that can
        // fail. The status code is arbitrary: series for other codes show up
        // once a request fails with them.
        for name in RequestMetricName::failable() {
            rpc_failure_count.add(0, &failure_attributes(name, tonic::Code::Internal));
        }
        // Histograms with attributes keep one startup point, in a dedicated
        // `test` series, so their first export has a single point: the host's
        // OTel-to-streamz bridge derives streamz columns per point and is
        // suspected to mishandle a multi-point first export (cl/993882996).
        // Histograms without attributes always export one point, so they
        // aren't pre-seeded.
        rpc_latency.record(1, &[KeyValue::new("request_type", "test")]);
        db_init_latency.record(1, &[KeyValue::new("db_size_bucket", "test")]);
        db_connect_retries.add(0, &[]);
        db_persist_failures.add(0, &[]);
        decrypt_dek_failures.add(0, &[]);
        user_info_deserialization_failures.add(0, &[]);
        db_decryption_failures.add(0, &[]);
        db_persist_queue_size.record(0, &[]);
        db_rebase_operation_failures.add(0, &[]);
        db_cleanup_failures.add(0, &[]);
        tls_handshake_failures.add(0, &[]);
        tls_receive_failures.add(0, &[]);
        persistence_enqueue_failures.add(0, &[]);
        session_rejected_low_memory.add(0, &[]);
        for reason in SessionRejectReason::ALL {
            session_rejected.add(0, &[KeyValue::new("reason", reason.as_str())]);
        }
        active_sessions.record(0, &[]);
        max_active_sessions.record(0, &[]);
        process_map_count.record(0, &[]);
        let orphaned_blob_deletes = meter
            .u64_counter("orphaned_blob_deletes")
            .with_description("Number of blobs that should have been soft-deleted but were not.")
            .build();
        let db_resource_exhausted_retries = meter
            .u64_counter("db_resource_exhausted_retries")
            .with_description(
                "Number of database calls retried after the host rejected them with \
                 RESOURCE_EXHAUSTED.",
            )
            .build();

        let icing_init_status = meter
            .u64_counter("icing_init_status")
            .with_description("Icing init status code.")
            .build();
        let icing_init_latency_ms =
            meter.u64_histogram("icing_init_latency_ms").with_description("Latency in ms.").build();
        let icing_recovery_cause = meter
            .u64_counter("icing_recovery_cause")
            .with_description("Icing recovery causes.")
            .build();
        let icing_recovery_latency_ms = meter
            .u64_histogram("icing_recovery_latency_ms")
            .with_description("Latency by recovery phase.")
            .build();
        let icing_num_previous_init_failures = meter
            .u64_histogram("icing_num_previous_init_failures")
            .with_description("Previous failure count.")
            .build();
        let icing_num_failed_reindexed_documents = meter
            .u64_histogram("icing_num_failed_reindexed_documents")
            .with_description("Failed reindex count.")
            .build();

        orphaned_blob_deletes.add(0, &[]);
        db_resource_exhausted_retries.add(0, &[]);

        // Created after the instruments above: the host OTel->streamz bridge
        // drops every instrument after the first one that fails to export, so
        // a new instrument that the host doesn't allowlist yet can't take down
        // the others.
        let db_pull_skipped_count = meter
            .u64_counter("db_pull_skipped_count")
            .with_description(
                "Number of database syncs that skipped downloading the database because it was \
                 unchanged.",
            )
            .build();
        db_pull_skipped_count.add(0, &[]);

        // Row locks: not allowlisted by the host until http://cl/1007520661, so
        // also created last, for the same reason as db_pull_skipped_count.
        let db_persist_lock_conflict_count = meter
            .u64_counter("db_persist_lock_conflict_count")
            .with_description(
                "Number of persist attempts rejected with ABORTED because the user's row was \
                 locked by a concurrent holder.",
            )
            .build();

        let db_persist_lock_wait_latency = meter
            .u64_histogram("db_persist_lock_wait_latency")
            .with_description("Time a persist spent waiting for a held row lock to be released.")
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();
        db_persist_lock_conflict_count.add(0, &[]);

        // DEK rotation: not allowlisted by the host until http://cl/1007520661,
        // so also created last, for the same reason as db_pull_skipped_count.
        let dek_rotation_count = meter
            .u64_counter("dek_rotation_count")
            .with_description(
                "Total number of DEK rotation requests handled, by response_type. Requests \
                 rejected by admission control are only counted in rpc_failure_count.",
            )
            .build();
        let dek_rotation_blobs_reencrypted_total = meter
            .u64_counter("dek_rotation_blobs_reencrypted_total")
            .with_description(
                "Cumulative count of memory blobs re-encrypted by successful DEK rotations.",
            )
            .build();
        let dek_rotation_bytes_reencrypted_total = meter
            .u64_counter("dek_rotation_bytes_reencrypted_total")
            .with_description("Cumulative ciphertext bytes written by successful DEK rotations.")
            .with_unit("By")
            .build();
        let dek_rotation_lock_extend_failures = meter
            .u64_counter("dek_rotation_lock_extend_failures")
            .with_description("Number of times a DEK rotation lost its row lock lease.")
            .build();
        let dek_rotation_blobs_per_run = meter
            .u64_histogram("dek_rotation_blobs_per_run")
            .with_description("Memory blobs re-encrypted by a single successful DEK rotation.")
            .with_boundaries(COUNT_BOUNDARIES.to_vec())
            .build();
        let dek_rotation_bytes_per_run = meter
            .u64_histogram("dek_rotation_bytes_per_run")
            .with_description("Ciphertext bytes written by a single successful DEK rotation.")
            .with_unit("By")
            .with_boundaries(DB_SIZE_BYTES_BOUNDARIES.to_vec())
            .build();
        let dek_rotation_throughput_bytes_per_sec = meter
            .u64_histogram("dek_rotation_throughput_bytes_per_sec")
            .with_description("Ciphertext bytes per second of a successful DEK rotation.")
            .with_unit("By/s")
            .with_boundaries(BYTES_PER_SEC_BOUNDARIES.to_vec())
            .build();
        let dek_rotation_latency_ms = meter
            .u64_histogram("dek_rotation_latency_ms")
            .with_description("End-to-end latency of DEK rotation, by status and size tiers.")
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();
        for response_type in DekRotationResponseType::ALL {
            dek_rotation_count.add(0, &[KeyValue::new("response_type", response_type.as_str())]);
        }
        dek_rotation_blobs_reencrypted_total.add(0, &[]);
        dek_rotation_bytes_reencrypted_total.add(0, &[]);
        dek_rotation_lock_extend_failures.add(0, &[]);
        dek_rotation_latency_ms.record(
            1,
            &[
                KeyValue::new("status", "test"),
                KeyValue::new("bytes_tier", "test"),
                KeyValue::new("blobs_tier", "test"),
            ],
        );

        Self {
            rpc_count,
            rpc_failure_count,
            rpc_latency,
            db_size,
            db_init_latency,
            db_cleanup_latency,
            db_cleanup_count,
            db_persist_latency,
            db_persist_latency_with_retries,
            db_persist_attempts,
            db_connect_retries,
            db_persist_failures,
            db_resource_exhausted_retries,
            db_persist_lock_conflict_count,
            db_persist_lock_wait_latency,
            decrypt_dek_failures,
            user_info_deserialization_failures,
            db_decryption_failures,
            db_persist_queue_size,
            db_persist_queue_count: Mutex::new(0),
            db_optimize_latency,
            db_save_speed,
            db_load_speed,
            key_sync_db_fetch_latency,
            key_sync_decrypt_latency,
            db_rebase_operation_failures,
            db_cleanup_failures,
            tls_handshake_failures,
            tls_receive_failures,
            persistence_enqueue_failures,
            orphaned_blob_deletes,
            session_rejected_low_memory,
            session_rejected,
            active_sessions,
            max_active_sessions,
            process_map_count,
            icing_init_status,
            icing_init_latency_ms,
            icing_recovery_cause,
            icing_recovery_latency_ms,
            icing_num_previous_init_failures,
            icing_num_failed_reindexed_documents,
            db_pull_skipped_count,
            dek_rotation_count,
            dek_rotation_blobs_reencrypted_total,
            dek_rotation_bytes_reencrypted_total,
            dek_rotation_lock_extend_failures,
            dek_rotation_blobs_per_run,
            dek_rotation_bytes_per_run,
            dek_rotation_throughput_bytes_per_sec,
            dek_rotation_latency_ms,
        }
    }

    /// Increment the number of requests received of the given type.
    /// This should be called unconditionally for the given metric name, whether
    /// the request fails or not.
    ///
    /// The special [`RequestMetricName::total`] should be incremented in
    /// addition to the specific request type, except for
    /// [`RequestMetricName::session_start`], which counts session streams
    /// rather than the messages sent on them.
    pub fn inc_requests(&self, name: RequestMetricName) {
        self.rpc_count.add(1, &[KeyValue::new("request_type", name)]);
    }

    /// Record a failed request, labelled with the gRPC status `code` it failed
    /// with.
    ///
    /// Call this exactly once per failed request, with the most specific
    /// request type known where it failed. The failure is also recorded under
    /// [`RequestMetricName::total`], except for session start failures, which
    /// are not mirrored into the total (just like their request count). Pass
    /// [`RequestMetricName::total`] itself for failures that cannot be
    /// attributed to a more specific request type; those are recorded once.
    pub fn record_failure(&self, name: RequestMetricName, code: tonic::Code) {
        let aggregated_in_total = name.is_aggregated_in_total();
        self.rpc_failure_count.add(1, &failure_attributes(name, code));
        if aggregated_in_total {
            self.rpc_failure_count.add(1, &failure_attributes(RequestMetricName::total(), code));
        }
    }

    /// Record a latency value for the given request.
    /// Calling this function will automatically record latency for the "total"
    /// requests group as well. Passing [`RequestMetricName::total`] itself
    /// records the latency once, under the total.
    pub fn record_latency(&self, elapsed_time_ms: u64, name: RequestMetricName) {
        // Round up as 1ms.
        let elapsed_time_ms = std::cmp::max(1, elapsed_time_ms);

        if !matches!(name.0, RequestMetricNameInner::Total) {
            self.rpc_latency.record(elapsed_time_ms, &[KeyValue::new("request_type", name)]);
        }
        self.rpc_latency.record(elapsed_time_ms, &[KeyValue::new("request_type", "total")]);
    }

    /// Record the time it took to save the DB.
    pub fn record_db_save_speed(&self, speed: u64) {
        // Round up as 1.
        let speed = std::cmp::max(1, speed);

        self.db_save_speed.record(speed, &[]);
    }

    /// Record the time it took to optimize the DB.
    pub fn record_db_optimize_latency(&self, latency: u64) {
        self.db_optimize_latency.record(latency, &[]);
    }

    /// Record the time it took to load the DB.
    pub fn record_db_load_speed(&self, speed: u64) {
        // Round up as 1.
        let speed = std::cmp::max(1, speed);

        self.db_load_speed.record(speed, &[]);
    }

    pub fn record_db_size(&self, size: u64) {
        self.db_size.record(size, &[]);
    }

    pub fn record_db_init_latency(&self, latency: u64, db_size_bucket: &'static str) {
        self.db_init_latency.record(latency, &[KeyValue::new("db_size_bucket", db_size_bucket)]);
    }

    pub fn record_db_cleanup_latency(&self, latency: u64) {
        self.db_cleanup_latency.record(latency, &[]);
    }

    pub fn record_db_cleanup_count(&self, count: u64) {
        self.db_cleanup_count.record(count, &[]);
    }

    pub fn record_db_persist_latency(&self, latency: u64) {
        self.db_persist_latency.record(latency, &[]);
    }

    pub fn record_db_persist_latency_with_retries(&self, latency: u64) {
        self.db_persist_latency_with_retries.record(latency, &[]);
    }

    pub fn record_db_persist_attempts(&self, attempts: u64) {
        self.db_persist_attempts.record(attempts, &[]);
    }

    pub fn inc_db_connect_retries(&self) {
        self.db_connect_retries.add(1, &[]);
    }

    pub fn inc_db_persist_failures(&self) {
        self.db_persist_failures.add(1, &[]);
    }

    /// Records that a database call is retried because the host rejected it
    /// with `RESOURCE_EXHAUSTED`.
    pub fn inc_db_resource_exhausted_retries(&self) {
        self.db_resource_exhausted_retries.add(1, &[]);
    }

    pub fn inc_db_persist_lock_conflicts(&self) {
        self.db_persist_lock_conflict_count.add(1, &[]);
    }

    pub fn record_db_persist_lock_wait_latency(&self, latency_ms: u64) {
        self.db_persist_lock_wait_latency.record(latency_ms, &[]);
    }

    pub fn inc_decrypt_dek_failures(&self) {
        self.decrypt_dek_failures.add(1, &[]);
    }

    pub fn inc_user_info_deserialization_failures(&self) {
        self.user_info_deserialization_failures.add(1, &[]);
    }

    pub fn inc_db_decryption_failures(&self) {
        self.db_decryption_failures.add(1, &[]);
    }

    /// Records the number of sessions waiting to be persisted, as counted by
    /// the persistence worker: the sessions in its queue plus the ones it took
    /// off the queue that are waiting for a slot or out a row lock. This also
    /// resets the count that [`Self::inc_db_persist_queue_size`] and
    /// [`Self::dec_db_persist_queue_size`] update, so that it can't drift.
    pub fn record_db_persist_queue_size(&self, size: u64) {
        self.update_db_persist_queue_size(|_| size);
    }

    /// Records that a session is about to be added to the database persist
    /// queue.
    pub fn inc_db_persist_queue_size(&self) {
        self.update_db_persist_queue_size(|count| count.saturating_add(1));
    }

    /// Records that a session counted by [`Self::inc_db_persist_queue_size`]
    /// could not be added to the database persist queue.
    pub fn dec_db_persist_queue_size(&self) {
        self.update_db_persist_queue_size(|count| count.saturating_sub(1));
    }

    fn update_db_persist_queue_size(&self, update: impl FnOnce(u64) -> u64) {
        let mut count = self.db_persist_queue_count.lock().unwrap_or_else(PoisonError::into_inner);
        *count = update(*count);
        self.db_persist_queue_size.record(*count, &[]);
    }

    pub fn record_key_sync_db_fetch_latency(&self, latency_ms: u64) {
        self.key_sync_db_fetch_latency.record(latency_ms, &[]);
    }

    pub fn record_key_sync_decrypt_latency(&self, latency_ms: u64) {
        self.key_sync_decrypt_latency.record(latency_ms, &[]);
    }

    pub fn inc_db_rebase_operation_failures(&self, count: u64) {
        self.db_rebase_operation_failures.add(count, &[]);
    }

    pub fn inc_db_cleanup_failures(&self) {
        self.db_cleanup_failures.add(1, &[]);
    }

    pub fn inc_tls_handshake_failures(&self) {
        self.tls_handshake_failures.add(1, &[]);
    }

    pub fn inc_tls_receive_failures(&self) {
        self.tls_receive_failures.add(1, &[]);
    }

    pub fn inc_persistence_enqueue_failures(&self) {
        self.persistence_enqueue_failures.add(1, &[]);
    }

    pub fn inc_orphaned_blob_deletes(&self, count: u64) {
        self.orphaned_blob_deletes.add(count, &[]);
    }

    pub fn inc_db_pull_skipped_count(&self) {
        self.db_pull_skipped_count.add(1, &[]);
    }

    pub fn inc_session_rejected_low_memory(&self) {
        self.session_rejected_low_memory.add(1, &[]);
    }

    /// Records a session rejected by admission control. For
    /// [`SessionRejectReason::LowMemory`] this also increments the legacy
    /// `session_rejected_low_memory` counter, so existing dashboards keep
    /// working.
    pub fn inc_session_rejected(&self, reason: SessionRejectReason) {
        if reason == SessionRejectReason::LowMemory {
            self.inc_session_rejected_low_memory();
        }
        self.session_rejected.add(1, &[KeyValue::new("reason", reason.as_str())]);
    }

    pub fn record_active_sessions(&self, count: u64) {
        self.active_sessions.record(count, &[]);
    }

    pub fn record_max_active_sessions(&self, max: u64) {
        self.max_active_sessions.record(max, &[]);
    }

    pub fn record_process_map_count(&self, count: u64) {
        self.process_map_count.record(count, &[]);
    }

    pub fn record_icing_initialization_stats(&self, result: &icing::InitializeResultProto) {
        // Record Overall Execution Status
        let status_code = result.status.as_ref().and_then(|s| s.code).unwrap_or_default();
        let status_str = icing::status_proto::Code::try_from(status_code)
            .map(|c| c.as_str_name())
            .unwrap_or("UNKNOWN");
        self.icing_init_status.add(1, &[KeyValue::new("status_code", status_str)]);

        if let Some(stats) = &result.initialize_stats {
            // Overall Initialization Latency
            if let Some(lat) = stats.latency_ms {
                self.icing_init_latency_ms.record(lat as u64, &[]);
            }

            // 1. Centralized Recovery Cause tracking
            let record_cause = |component: &'static str, cause: Option<i32>| {
                if let Some(c) = cause {
                    let cause_str = icing::initialize_stats_proto::RecoveryCause::try_from(c)
                        .map(|eval| eval.as_str_name())
                        .unwrap_or("UNKNOWN");

                    self.icing_recovery_cause.add(
                        1,
                        &[KeyValue::new("component", component), KeyValue::new("cause", cause_str)],
                    );
                }
            };
            record_cause("document_store", stats.document_store_recovery_cause);
            record_cause("index", stats.index_restoration_cause);
            record_cause("schema_store", stats.schema_store_recovery_cause);
            record_cause("integer_index", stats.integer_index_restoration_cause);
            record_cause(
                "qualified_id_join_index",
                stats.qualified_id_join_index_restoration_cause,
            );
            record_cause("embedding_index", stats.embedding_index_restoration_cause);

            // 2. Centralized Recovery Latency tracking
            if let Some(lat) = stats.document_store_recovery_latency_ms {
                self.icing_recovery_latency_ms
                    .record(lat as u64, &[KeyValue::new("component", "document_store")]);
            }
            if let Some(lat) = stats.index_restoration_latency_ms {
                self.icing_recovery_latency_ms
                    .record(lat as u64, &[KeyValue::new("component", "index")]);
            }
            if let Some(lat) = stats.schema_store_recovery_latency_ms {
                self.icing_recovery_latency_ms
                    .record(lat as u64, &[KeyValue::new("component", "schema_store")]);
            }

            // 3. Failure & Reindex Distributions
            if let Some(failures) = stats.num_previous_init_failures {
                self.icing_num_previous_init_failures.record(failures as u64, &[]);
            }
            if let Some(failed_docs) = stats.num_failed_reindexed_documents {
                self.icing_num_failed_reindexed_documents.record(failed_docs as u64, &[]);
            }
        }
    }

    /// Counts one handled RotateDek request.
    pub fn inc_dek_rotation_count(&self, response_type: DekRotationResponseType) {
        self.dek_rotation_count.add(1, &[KeyValue::new("response_type", response_type.as_str())]);
    }

    /// Counts a DEK rotation losing its row lock lease.
    pub fn inc_dek_rotation_lock_extend_failures(&self) {
        self.dek_rotation_lock_extend_failures.add(1, &[]);
    }

    /// Records one DEK rotation that took `elapsed_ms`. A successful run
    /// updates the re-encryption totals, the per-run blob, byte and
    /// throughput histograms, and the latency histogram labeled with its
    /// size tiers; a failed run only records latency, with `unknown` tiers.
    /// `elapsed_ms` is raised to at least 1 so throughput is always
    /// defined.
    pub fn record_dek_rotation_run(&self, run: DekRotationRun, elapsed_ms: u64) {
        let elapsed_ms = elapsed_ms.max(1);
        let (status, bytes_tier, blobs_tier) = match run {
            DekRotationRun::Succeeded { blobs, ciphertext_bytes } => {
                self.dek_rotation_blobs_reencrypted_total.add(blobs, &[]);
                self.dek_rotation_bytes_reencrypted_total.add(ciphertext_bytes, &[]);
                self.dek_rotation_blobs_per_run.record(blobs, &[]);
                self.dek_rotation_bytes_per_run.record(ciphertext_bytes, &[]);
                self.dek_rotation_throughput_bytes_per_sec
                    .record(ciphertext_bytes.saturating_mul(1000) / elapsed_ms, &[]);
                (
                    "success",
                    bucket_dek_rotation_bytes(ciphertext_bytes),
                    bucket_dek_rotation_blobs(blobs),
                )
            }
            DekRotationRun::Failed => ("failure", "unknown", "unknown"),
        };
        self.dek_rotation_latency_ms.record(
            elapsed_ms,
            &[
                KeyValue::new("status", status),
                KeyValue::new("bytes_tier", bytes_tier),
                KeyValue::new("blobs_tier", blobs_tier),
            ],
        );
    }
}

/// Outcome of one DEK rotation, as recorded by
/// [`Metrics::record_dek_rotation_run`].
#[derive(Clone, Copy, Debug)]
pub enum DekRotationRun {
    Succeeded { blobs: u64, ciphertext_bytes: u64 },
    Failed,
}

/// Buckets the ciphertext bytes of a rotation into the `bytes_tier` label of
/// `dek_rotation_latency_ms`. Every tier includes its lower bound and excludes
/// its upper bound, except `100-250MB`, which also includes 250 MiB.
fn bucket_dek_rotation_bytes(bytes: u64) -> &'static str {
    let mb = MB as u64;
    match bytes {
        b if b < mb => "<1MB",
        b if b < 10 * mb => "1-10MB",
        b if b < 50 * mb => "10-50MB",
        b if b < 100 * mb => "50-100MB",
        b if b <= 250 * mb => "100-250MB",
        _ => "250MB+",
    }
}

/// Buckets the re-encrypted blob count of a rotation into the `blobs_tier`
/// label of `dek_rotation_latency_ms`.
fn bucket_dek_rotation_blobs(blobs: u64) -> &'static str {
    match blobs {
        0..10 => "<10",
        10..50 => "10-50",
        50..200 => "50-200",
        200..1000 => "200-1000",
        _ => "1000+",
    }
}

/// Buckets a database size (in bytes) into a human-readable label for use as
/// a metric attribute. Uses 10MB increments up to 100MB.
pub fn bucket_db_size(size_bytes: usize) -> &'static str {
    match size_bytes {
        size if size <= 100 * KB => "0-100KB",
        size if size <= 10 * MB => "100KB-10MB",
        size if size <= 20 * MB => "10MB-20MB",
        size if size <= 30 * MB => "20MB-30MB",
        size if size <= 40 * MB => "30MB-40MB",
        size if size <= 50 * MB => "40MB-50MB",
        size if size <= 60 * MB => "50MB-60MB",
        size if size <= 70 * MB => "60MB-70MB",
        size if size <= 80 * MB => "70MB-80MB",
        size if size <= 90 * MB => "80MB-90MB",
        size if size <= 100 * MB => "90MB-100MB",
        _ => "100MB+",
    }
}

/// The speed in KB/ms of transferring `bytes` in `elapsed`, for
/// `db_save_speed` and `db_load_speed`. Transfers faster than 1 ms count as
/// taking 1 ms.
pub fn transfer_speed_kb_per_ms(bytes: usize, elapsed: std::time::Duration) -> u64 {
    let elapsed_ms = std::cmp::max(1, elapsed.as_millis() as u64);
    (bytes / KB) as u64 / elapsed_ms
}

fn create_metrics() -> (OakObserver, Arc<Metrics>) {
    let observer =
        OakObserver::create("http://10.0.2.100:8080".to_string(), "sealed_memory_service", vec![])
            .unwrap();
    let metrics = Arc::new(Metrics::new(&observer.meter));
    (observer, metrics)
}

lazy_static! {
    static ref GLOBAL_METRICS: (OakObserver, Arc<Metrics>) = create_metrics();
}

pub fn get_global_metrics() -> Arc<Metrics> {
    GLOBAL_METRICS.1.clone()
}

fn get_name<T: Name>(_x: &T) -> String {
    T::NAME.to_string()
}

/// Returns the `status_code` label of the gRPC status `code`: its canonical
/// name (e.g. `INVALID_ARGUMENT`), as defined in
/// https://github.com/googleapis/googleapis/blob/master/google/rpc/code.proto.
///
/// The host's pstreamz policy allows the `status_code` column because it only
/// ever holds one of these 17 values, and names this function as their source
/// of truth. Never label failures with anything else, such as status messages.
fn status_code_label(code: tonic::Code) -> &'static str {
    match code {
        tonic::Code::Ok => "OK",
        tonic::Code::Cancelled => "CANCELLED",
        tonic::Code::Unknown => "UNKNOWN",
        tonic::Code::InvalidArgument => "INVALID_ARGUMENT",
        tonic::Code::DeadlineExceeded => "DEADLINE_EXCEEDED",
        tonic::Code::NotFound => "NOT_FOUND",
        tonic::Code::AlreadyExists => "ALREADY_EXISTS",
        tonic::Code::PermissionDenied => "PERMISSION_DENIED",
        tonic::Code::ResourceExhausted => "RESOURCE_EXHAUSTED",
        tonic::Code::FailedPrecondition => "FAILED_PRECONDITION",
        tonic::Code::Aborted => "ABORTED",
        tonic::Code::OutOfRange => "OUT_OF_RANGE",
        tonic::Code::Unimplemented => "UNIMPLEMENTED",
        tonic::Code::Internal => "INTERNAL",
        tonic::Code::Unavailable => "UNAVAILABLE",
        tonic::Code::DataLoss => "DATA_LOSS",
        tonic::Code::Unauthenticated => "UNAUTHENTICATED",
    }
}

/// The attributes identifying an `rpc_failure_count` series.
///
/// Every point must carry exactly these two string attributes: the host
/// derives the metric's streamz columns from a single exported point.
fn failure_attributes(name: RequestMetricName, code: tonic::Code) -> [KeyValue; 2] {
    [KeyValue::new("request_type", name), KeyValue::new("status_code", status_code_label(code))]
}

impl From<RequestMetricName> for Value {
    fn from(name: RequestMetricName) -> Value {
        match name.0 {
            RequestMetricNameInner::SealedMemoryRequest(variant) => variant.into(),
            RequestMetricNameInner::Handshake => "Handshake".into(),
            RequestMetricNameInner::Total => "total".into(),
            RequestMetricNameInner::DecryptionFailure => "DecryptionFailure".into(),
            RequestMetricNameInner::DeserializationFailure => "DeserializationFailure".into(),
            RequestMetricNameInner::EmptyTlsFrame => "EmptyTlsFrame".into(),
            RequestMetricNameInner::EmptyRequest => "EmptyRequest".into(),
            RequestMetricNameInner::SessionStart => "SessionStart".into(),
        }
    }
}

impl RequestMetricName {
    pub fn total() -> RequestMetricName {
        RequestMetricName(RequestMetricNameInner::Total)
    }

    pub fn handshake() -> RequestMetricName {
        RequestMetricName(RequestMetricNameInner::Handshake)
    }

    pub fn decryption_failure() -> RequestMetricName {
        RequestMetricName(RequestMetricNameInner::DecryptionFailure)
    }

    pub fn deserialization_failure() -> RequestMetricName {
        RequestMetricName(RequestMetricNameInner::DeserializationFailure)
    }

    pub fn empty_tls_frame() -> RequestMetricName {
        RequestMetricName(RequestMetricNameInner::EmptyTlsFrame)
    }

    /// A request message that does not carry a request.
    pub fn empty_request() -> RequestMetricName {
        RequestMetricName(RequestMetricNameInner::EmptyRequest)
    }

    /// An attempt to open a session stream, on any of the session RPCs.
    pub fn session_start() -> RequestMetricName {
        RequestMetricName(RequestMetricNameInner::SessionStart)
    }

    pub fn new_sealed_memory_request(
        variant: &sealed_memory_request::Request,
    ) -> RequestMetricName {
        RequestMetricName(RequestMetricNameInner::SealedMemoryRequest(match variant {
            sealed_memory_request::Request::UserRegistrationRequest(r) => get_name(r),
            sealed_memory_request::Request::KeySyncRequest(r) => get_name(r),
            sealed_memory_request::Request::AddMemoryRequest(r) => get_name(r),
            sealed_memory_request::Request::AddMemoriesRequest(r) => get_name(r),
            #[allow(deprecated)]
            sealed_memory_request::Request::GetMemoriesRequest(r) => get_name(r),
            sealed_memory_request::Request::ResetMemoryRequest(r) => get_name(r),
            sealed_memory_request::Request::GetMemoryByIdRequest(r) => get_name(r),
            sealed_memory_request::Request::GetMemoryByNameRequest(r) => get_name(r),
            sealed_memory_request::Request::DeleteMemoryRequest(r) => get_name(r),
            sealed_memory_request::Request::GetMemoriesByIdRequest(r) => get_name(r),
            sealed_memory_request::Request::SearchMemoriesRequest(r) => get_name(r),
            sealed_memory_request::Request::GetDatabaseMetricsRequest(r) => get_name(r),
            sealed_memory_request::Request::SyncDatabaseRequest(r) => get_name(r),
        }))
    }

    /// Every request type that a failure can be recorded under.
    fn failable() -> impl Iterator<Item = RequestMetricName> {
        use sealed_memory_request::Request;
        // Every request variant, as listed in `new_sealed_memory_request`.
        #[allow(deprecated)]
        let variants = [
            Request::UserRegistrationRequest(Default::default()),
            Request::KeySyncRequest(Default::default()),
            Request::AddMemoryRequest(Default::default()),
            Request::AddMemoriesRequest(Default::default()),
            Request::GetMemoriesRequest(Default::default()),
            Request::ResetMemoryRequest(Default::default()),
            Request::GetMemoryByIdRequest(Default::default()),
            Request::GetMemoryByNameRequest(Default::default()),
            Request::DeleteMemoryRequest(Default::default()),
            Request::GetMemoriesByIdRequest(Default::default()),
            Request::SearchMemoriesRequest(Default::default()),
            Request::GetDatabaseMetricsRequest(Default::default()),
            Request::SyncDatabaseRequest(Default::default()),
        ];
        [
            Self::total(),
            Self::handshake(),
            Self::decryption_failure(),
            Self::deserialization_failure(),
            Self::empty_request(),
            Self::session_start(),
        ]
        .into_iter()
        .chain(variants.into_iter().map(|variant| Self::new_sealed_memory_request(&variant)))
    }

    /// Whether failures recorded under this name are also recorded under the
    /// total.
    fn is_aggregated_in_total(&self) -> bool {
        !matches!(self.0, RequestMetricNameInner::Total | RequestMetricNameInner::SessionStart)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dek_rotation_tiers_bucket_by_size() {
        let mb = MB as u64;
        let byte_cases = [
            (0, "<1MB"),
            (mb - 1, "<1MB"),
            (mb, "1-10MB"),
            (10 * mb - 1, "1-10MB"),
            (10 * mb, "10-50MB"),
            (50 * mb - 1, "10-50MB"),
            (50 * mb, "50-100MB"),
            (100 * mb - 1, "50-100MB"),
            (100 * mb, "100-250MB"),
            (250 * mb, "100-250MB"),
            (250 * mb + 1, "250MB+"),
            (u64::MAX, "250MB+"),
        ];
        for (bytes, tier) in byte_cases {
            assert_eq!(bucket_dek_rotation_bytes(bytes), tier, "{bytes} bytes");
        }

        let blob_cases = [
            (0, "<10"),
            (9, "<10"),
            (10, "10-50"),
            (49, "10-50"),
            (50, "50-200"),
            (199, "50-200"),
            (200, "200-1000"),
            (999, "200-1000"),
            (1000, "1000+"),
            (u64::MAX, "1000+"),
        ];
        for (blobs, tier) in blob_cases {
            assert_eq!(bucket_dek_rotation_blobs(blobs), tier, "{blobs} blobs");
        }
    }

    #[test]
    fn test_record_icing_initialization_stats() {
        let (_observer, metrics) = create_metrics();
        let result_proto = icing::InitializeResultProto {
            status: Some(icing::StatusProto {
                code: Some(icing::status_proto::Code::Ok as i32),
                message: Some("OK".to_string()),
            }),
            ..Default::default()
        };

        // This is a mockup; testing that it doesn't panic.
        metrics.record_icing_initialization_stats(&result_proto);
    }

    #[test]
    fn test_record_icing_initialization_stats_with_full_stats() {
        let (_observer, metrics) = create_metrics();
        let result_proto = icing::InitializeResultProto {
            status: Some(icing::StatusProto {
                code: Some(icing::status_proto::Code::Ok as i32),
                message: Some("OK".to_string()),
            }),
            initialize_stats: Some(icing::InitializeStatsProto {
                latency_ms: Some(150),
                document_store_recovery_cause: Some(1),
                index_restoration_cause: Some(2),
                schema_store_recovery_cause: Some(3),
                integer_index_restoration_cause: Some(4),
                qualified_id_join_index_restoration_cause: Some(0),
                embedding_index_restoration_cause: Some(999),
                document_store_recovery_latency_ms: Some(50),
                index_restoration_latency_ms: Some(25),
                schema_store_recovery_latency_ms: Some(15),
                num_previous_init_failures: Some(2),
                num_failed_reindexed_documents: Some(10),
                ..Default::default()
            }),
            ..Default::default()
        };

        // This should not panic and should record UNKNOWN for the unsupported code.
        metrics.record_icing_initialization_stats(&result_proto);
    }
}

/// Tests that read back the values exported by [`Metrics`].
///
/// Each test builds a fresh [`TestMetrics`] (see the `metrics_testing` crate),
/// which wires [`Metrics`] to a private in-memory meter provider, so tests are
/// deterministic and independent of each other and of the global metrics
/// singleton.
#[cfg(test)]
mod value_tests {
    use std::collections::{BTreeMap, BTreeSet};

    use metrics_testing::{Attrs, INF, attrs};

    use super::*;

    type TestMetrics = metrics_testing::TestMetrics<Metrics>;

    /// Returns [`Metrics`] wired to a private in-memory meter provider.
    fn test_metrics() -> TestMetrics {
        TestMetrics::new(Metrics::new)
    }

    /// A metric method that takes no arguments.
    type IncFn = fn(&Metrics);
    /// A metric method that takes a single value.
    type RecordFn = fn(&Metrics, u64);

    /// Counters that take no arguments and increment by one.
    const UNIT_COUNTERS: &[(&str, IncFn)] = &[
        ("db_connect_retries", Metrics::inc_db_connect_retries),
        ("db_persist_failures", Metrics::inc_db_persist_failures),
        ("db_resource_exhausted_retries", Metrics::inc_db_resource_exhausted_retries),
        ("db_persist_lock_conflict_count", Metrics::inc_db_persist_lock_conflicts),
        ("decrypt_dek_failures", Metrics::inc_decrypt_dek_failures),
        ("user_info_deserialization_failures", Metrics::inc_user_info_deserialization_failures),
        ("db_decryption_failures", Metrics::inc_db_decryption_failures),
        ("db_cleanup_failures", Metrics::inc_db_cleanup_failures),
        ("tls_handshake_failures", Metrics::inc_tls_handshake_failures),
        ("tls_receive_failures", Metrics::inc_tls_receive_failures),
        ("persistence_enqueue_failures", Metrics::inc_persistence_enqueue_failures),
        ("session_rejected_low_memory", Metrics::inc_session_rejected_low_memory),
        ("db_pull_skipped_count", Metrics::inc_db_pull_skipped_count),
        ("dek_rotation_lock_extend_failures", Metrics::inc_dek_rotation_lock_extend_failures),
    ];

    /// Counters that are incremented by a caller-provided amount.
    const AMOUNT_COUNTERS: &[(&str, RecordFn)] = &[
        ("db_rebase_operation_failures", Metrics::inc_db_rebase_operation_failures),
        ("orphaned_blob_deletes", Metrics::inc_orphaned_blob_deletes),
    ];

    /// Attribute-less millisecond latency histograms.
    const LATENCY_HISTOGRAMS: &[(&str, RecordFn)] = &[
        ("db_cleanup_latency", Metrics::record_db_cleanup_latency),
        ("db_persist_latency", Metrics::record_db_persist_latency),
        ("db_persist_latency_with_retries", Metrics::record_db_persist_latency_with_retries),
        ("db_persist_lock_wait_latency", Metrics::record_db_persist_lock_wait_latency),
        ("db_optimize_latency", Metrics::record_db_optimize_latency),
        ("key_sync_db_fetch_latency", Metrics::record_key_sync_db_fetch_latency),
        ("key_sync_decrypt_latency", Metrics::record_key_sync_decrypt_latency),
    ];

    /// Count histograms.
    const COUNT_HISTOGRAMS: &[(&str, RecordFn)] = &[
        ("db_cleanup_count", Metrics::record_db_cleanup_count),
        ("db_persist_attempts", Metrics::record_db_persist_attempts),
    ];

    /// Speed histograms.
    const SPEED_HISTOGRAMS: &[(&str, RecordFn)] = &[
        ("db_save_speed", Metrics::record_db_save_speed),
        ("db_load_speed", Metrics::record_db_load_speed),
    ];

    /// The `rpc_failure_count` series for `request_type` and `status_code`.
    fn failure_series(request_type: &str, status_code: &str) -> Attrs {
        attrs(&[("request_type", request_type), ("status_code", status_code)])
    }

    /// Every `request_type` that a failure can be recorded under.
    const FAILABLE_REQUEST_TYPES: &[&str] = &[
        "total",
        "Handshake",
        "DecryptionFailure",
        "DeserializationFailure",
        "EmptyRequest",
        "SessionStart",
        "UserRegistrationRequest",
        "KeySyncRequest",
        "AddMemoryRequest",
        "AddMemoriesRequest",
        "GetMemoriesRequest",
        "ResetMemoryRequest",
        "GetMemoryByIdRequest",
        "GetMemoryByNameRequest",
        "DeleteMemoryRequest",
        "GetMemoriesByIdRequest",
        "SearchMemoriesRequest",
        "GetDatabaseMetricsRequest",
        "SyncDatabaseRequest",
    ];

    #[test]
    fn startup_exports_zero_initialized_instruments() {
        let harness = test_metrics();
        let snapshot = harness.collect();

        let empty: &[(&str, &str)] = &[];

        // Counters start at zero.
        assert_eq!(
            snapshot.counter_points("rpc_count"),
            &BTreeMap::from([
                (attrs(&[("request_type", "total")]), 0),
                (attrs(&[("request_type", "SessionStart")]), 0),
            ])
        );
        // Every request type that can fail has a failure series, under an
        // arbitrary status code.
        let failures: BTreeMap<Attrs, u64> = FAILABLE_REQUEST_TYPES
            .iter()
            .map(|request_type| (failure_series(request_type, "INTERNAL"), 0))
            .collect();
        assert_eq!(failures.len(), 19);
        assert_eq!(snapshot.counter_points("rpc_failure_count"), &failures);
        let zeroed_counters = UNIT_COUNTERS
            .iter()
            .map(|(metric_name, _)| *metric_name)
            .chain(AMOUNT_COUNTERS.iter().map(|(metric_name, _)| *metric_name));
        for name in zeroed_counters {
            assert_eq!(
                snapshot.counter_points(name),
                &BTreeMap::from([(attrs(empty), 0)]),
                "{name}"
            );
        }

        // The gauges start at zero.
        for name in
            ["db_persist_queue_size", "active_sessions", "max_active_sessions", "process_map_count"]
        {
            assert_eq!(snapshot.gauge_points(name), &BTreeMap::from([(attrs(empty), 0)]), "{name}");
        }
        // Every DEK rotation outcome has a series, and the rotation totals
        // start at zero.
        assert_eq!(
            snapshot.counter_points("dek_rotation_count"),
            &DekRotationResponseType::ALL
                .iter()
                .map(|response_type| (attrs(&[("response_type", response_type.as_str())]), 0))
                .collect::<BTreeMap<_, _>>()
        );
        for name in ["dek_rotation_blobs_reencrypted_total", "dek_rotation_bytes_reencrypted_total"]
        {
            assert_eq!(
                snapshot.counter_points(name),
                &BTreeMap::from([(attrs(empty), 0)]),
                "{name}"
            );
        }
        // Every admission-control rejection reason has a series.
        assert_eq!(
            snapshot.counter_points("session_rejected"),
            &SessionRejectReason::ALL
                .iter()
                .map(|reason| (attrs(&[("reason", reason.as_str())]), 0))
                .collect::<BTreeMap<_, _>>()
        );

        // Attribute `(key, value)` pairs, as written in the table below.
        type Pairs<'a> = &'a [(&'a str, &'a str)];

        // Histograms with attributes carry a single sample at startup, in a
        // dedicated `test` series (see `Metrics::new`).
        let startup_histograms: &[(&str, Pairs)] = &[
            ("rpc_latency", &[("request_type", "test")]),
            ("db_init_latency", &[("db_size_bucket", "test")]),
            (
                "dek_rotation_latency_ms",
                &[("status", "test"), ("bytes_tier", "test"), ("blobs_tier", "test")],
            ),
        ];
        for (name, pairs) in startup_histograms {
            let points = snapshot.histogram_points(name);
            assert_eq!(points.len(), 1, "{name}: {points:?}");
            let point = snapshot.histogram(name, pairs);
            assert_eq!((point.count, point.sum), (1, 1), "{name}");
        }

        // Instruments that are only exported once recorded.
        let expected: BTreeSet<&str> = [
            "rpc_count",
            "rpc_failure_count",
            "db_persist_queue_size",
            "session_rejected",
            "active_sessions",
            "max_active_sessions",
            "process_map_count",
            "dek_rotation_count",
            "dek_rotation_blobs_reencrypted_total",
            "dek_rotation_bytes_reencrypted_total",
        ]
        .into_iter()
        .chain(UNIT_COUNTERS.iter().map(|(metric_name, _)| *metric_name))
        .chain(AMOUNT_COUNTERS.iter().map(|(metric_name, _)| *metric_name))
        .chain(startup_histograms.iter().map(|(metric_name, _)| *metric_name))
        .collect();
        assert_eq!(snapshot.names(), expected);
        // Histograms without attributes have no startup sample, so that none
        // of their samples is fake: they are exported from their first
        // recording on, like the icing instruments.
        let unrecorded = [
            "db_size",
            "db_save_speed",
            "db_load_speed",
            "icing_init_status",
            "icing_init_latency_ms",
            "icing_recovery_cause",
            "icing_recovery_latency_ms",
            "icing_num_previous_init_failures",
            "icing_num_failed_reindexed_documents",
            "dek_rotation_blobs_per_run",
            "dek_rotation_bytes_per_run",
            "dek_rotation_throughput_bytes_per_sec",
        ]
        .into_iter()
        .chain(LATENCY_HISTOGRAMS.iter().map(|(metric_name, _)| *metric_name))
        .chain(COUNT_HISTOGRAMS.iter().map(|(metric_name, _)| *metric_name));
        for name in unrecorded {
            assert!(!snapshot.names().contains(name), "{name} unexpectedly exported at startup");
        }
    }

    /// Returns the bucket boundaries the SDK gives a histogram that does not
    /// configure its own, read from a probe histogram instead of copying
    /// the SDK's default values into this test.
    fn otel_default_histogram_boundaries() -> Vec<f64> {
        let harness = metrics_testing::TestMetrics::new(|meter| {
            meter.u64_histogram("default_boundaries_probe").build()
        });
        harness.metrics.record(0, &[]);
        harness.collect().histogram("default_boundaries_probe", &[]).bounds.clone()
    }

    #[derive(Debug)]
    enum Kind<'a> {
        Counter,
        Gauge,
        Histogram(&'a [f64]),
    }

    #[test]
    fn instrument_names_units_descriptions_and_boundaries() {
        let harness = test_metrics();
        let metrics = &harness.metrics;
        // Record into every instrument so that all of them are exported.
        metrics.record_db_size(1);
        for (_, record) in LATENCY_HISTOGRAMS.iter().chain(COUNT_HISTOGRAMS).chain(SPEED_HISTOGRAMS)
        {
            record(metrics, 1);
        }
        let init = icing::InitializeResultProto {
            initialize_stats: Some(icing::InitializeStatsProto {
                latency_ms: Some(1),
                document_store_recovery_cause: Some(1),
                document_store_recovery_latency_ms: Some(1),
                num_previous_init_failures: Some(1),
                num_failed_reindexed_documents: Some(1),
                ..Default::default()
            }),
            ..Default::default()
        };
        metrics.record_icing_initialization_stats(&init);
        metrics.record_dek_rotation_run(
            DekRotationRun::Succeeded { blobs: 1, ciphertext_bytes: 1 },
            1,
        );
        let snapshot = harness.collect();

        let default_bounds = otel_default_histogram_boundaries();
        use Kind::*;
        let expected: &[(&str, &str, &str, Kind)] = &[
            (
                "rpc_count",
                "",
                "Total number of RPCs received by the private memory server.",
                Counter,
            ),
            ("rpc_failure_count", "", "Number of RPCs that failed.", Counter),
            (
                "rpc_latency",
                "ms",
                "Latency in ms of handling each application request, excluding the handshake, \
                 decryption and encryption.",
                Histogram(LATENCY_MS_BOUNDARIES),
            ),
            (
                "db_size",
                "By",
                "Size in bytes of the encrypted database, recorded when key sync loads it and each \
                 time it is persisted.",
                Histogram(DB_SIZE_BYTES_BOUNDARIES),
            ),
            (
                "db_init_latency",
                "ms",
                "Latency of Icing database initialization.",
                Histogram(LATENCY_MS_BOUNDARIES),
            ),
            (
                "db_cleanup_latency",
                "ms",
                "Latency of expired memories cleanup operation.",
                Histogram(LATENCY_MS_BOUNDARIES),
            ),
            (
                "db_cleanup_count",
                "",
                "Number of expired memories cleaned up during cleanup operation.",
                Histogram(COUNT_BOUNDARIES),
            ),
            (
                "db_persist_latency",
                "ms",
                "Latency of persisting the database.",
                Histogram(LATENCY_MS_BOUNDARIES),
            ),
            (
                "db_persist_latency_with_retries",
                "ms",
                "Latency of persisting the database including all retry attempts.",
                Histogram(LATENCY_MS_BOUNDARIES),
            ),
            (
                "db_persist_attempts",
                "",
                "Number of attempts before metadata persist succeeds.",
                Histogram(COUNT_BOUNDARIES),
            ),
            (
                "db_connect_retries",
                "",
                "Number of retries when connecting to the database.",
                Counter,
            ),
            (
                "db_persist_failures",
                "",
                "Number of failures when persisting the database.",
                Counter,
            ),
            (
                "db_persist_lock_conflict_count",
                "",
                "Number of persist attempts rejected with ABORTED because the user's row was \
                 locked by a concurrent holder.",
                Counter,
            ),
            (
                "db_persist_lock_wait_latency",
                "ms",
                "Time a persist spent waiting for a held row lock to be released.",
                Histogram(LATENCY_MS_BOUNDARIES),
            ),
            (
                "db_decryption_failures",
                "",
                "Number of failures when decrypting the database.",
                Counter,
            ),
            ("db_persist_queue_size", "", "Number of items in the database persist queue.", Gauge),
            ("decrypt_dek_failures", "", "Number of failures when decrypting the DEK.", Counter),
            (
                "user_info_deserialization_failures",
                "",
                "Number of failures when deserializing user info.",
                Counter,
            ),
            (
                "db_optimize_latency",
                "ms",
                "Latency of optimizing the database.",
                Histogram(LATENCY_MS_BOUNDARIES),
            ),
            (
                "db_save_speed",
                "KB/ms",
                "Speed of saving the database.",
                Histogram(SPEED_KB_PER_MS_BOUNDARIES),
            ),
            (
                "db_load_speed",
                "KB/ms",
                "Speed of loading the database.",
                Histogram(SPEED_KB_PER_MS_BOUNDARIES),
            ),
            (
                "key_sync_db_fetch_latency",
                "ms",
                "Latency of fetching metadata blob from external DB.",
                Histogram(LATENCY_MS_BOUNDARIES),
            ),
            (
                "key_sync_decrypt_latency",
                "ms",
                "Latency of decrypting the database.",
                Histogram(LATENCY_MS_BOUNDARIES),
            ),
            (
                "db_rebase_operation_failures",
                "",
                "Number of operations that failed to replay during DB rebase.",
                Counter,
            ),
            (
                "db_cleanup_failures",
                "",
                "Number of failures when cleaning expired memories.",
                Counter,
            ),
            ("tls_handshake_failures", "", "Number of TLS handshake failures.", Counter),
            ("tls_receive_failures", "", "Number of TLS data receive errors.", Counter),
            (
                "persistence_enqueue_failures",
                "",
                "Number of failures enqueueing sessions for persistence.",
                Counter,
            ),
            (
                "orphaned_blob_deletes",
                "",
                "Number of blobs that should have been soft-deleted but were not.",
                Counter,
            ),
            (
                "db_resource_exhausted_retries",
                "",
                "Number of database calls retried after the host rejected them with \
                 RESOURCE_EXHAUSTED.",
                Counter,
            ),
            (
                "session_rejected_low_memory",
                "",
                "Number of sessions rejected due to low memory.",
                Counter,
            ),
            (
                "session_rejected",
                "",
                "Number of new sessions rejected by admission control, by reason.",
                Counter,
            ),
            (
                "active_sessions",
                "",
                "Number of currently live sessions (each may own an Icing instance).",
                Gauge,
            ),
            ("max_active_sessions", "", "Configured cap on live sessions per enclave.", Gauge),
            (
                "process_map_count",
                "",
                "Number of memory mappings of the process (lines in /proc/self/maps).",
                Gauge,
            ),
            ("icing_init_status", "", "Icing init status code.", Counter),
            // TODO: b/571198870 - the icing `*_ms` histograms have no unit and
            // use the OpenTelemetry default boundaries (max finite 10 s). Left
            // to Gerrit change 52200, which sets their units and boundaries.
            ("icing_init_latency_ms", "", "Latency in ms.", Histogram(&default_bounds)),
            ("icing_recovery_cause", "", "Icing recovery causes.", Counter),
            (
                "icing_recovery_latency_ms",
                "",
                "Latency by recovery phase.",
                Histogram(&default_bounds),
            ),
            (
                "icing_num_previous_init_failures",
                "",
                "Previous failure count.",
                Histogram(&default_bounds),
            ),
            (
                "icing_num_failed_reindexed_documents",
                "",
                "Failed reindex count.",
                Histogram(&default_bounds),
            ),
            (
                "db_pull_skipped_count",
                "",
                "Number of database syncs that skipped downloading the database because it was \
                 unchanged.",
                Counter,
            ),
            (
                "dek_rotation_count",
                "",
                "Total number of DEK rotation requests handled, by response_type. Requests \
                 rejected by admission control are only counted in rpc_failure_count.",
                Counter,
            ),
            (
                "dek_rotation_blobs_reencrypted_total",
                "",
                "Cumulative count of memory blobs re-encrypted by successful DEK rotations.",
                Counter,
            ),
            (
                "dek_rotation_bytes_reencrypted_total",
                "By",
                "Cumulative ciphertext bytes written by successful DEK rotations.",
                Counter,
            ),
            (
                "dek_rotation_lock_extend_failures",
                "",
                "Number of times a DEK rotation lost its row lock lease.",
                Counter,
            ),
            (
                "dek_rotation_blobs_per_run",
                "",
                "Memory blobs re-encrypted by a single successful DEK rotation.",
                Histogram(COUNT_BOUNDARIES),
            ),
            (
                "dek_rotation_bytes_per_run",
                "By",
                "Ciphertext bytes written by a single successful DEK rotation.",
                Histogram(DB_SIZE_BYTES_BOUNDARIES),
            ),
            (
                "dek_rotation_throughput_bytes_per_sec",
                "By/s",
                "Ciphertext bytes per second of a successful DEK rotation.",
                Histogram(BYTES_PER_SEC_BOUNDARIES),
            ),
            (
                "dek_rotation_latency_ms",
                "ms",
                "End-to-end latency of DEK rotation, by status and size tiers.",
                Histogram(LATENCY_MS_BOUNDARIES),
            ),
        ];

        assert_eq!(
            snapshot.names(),
            expected.iter().map(|(metric_name, ..)| *metric_name).collect::<BTreeSet<_>>()
        );
        for (name, unit, description, kind) in expected {
            let metric = snapshot.get(name);
            assert_eq!(metric.unit, *unit, "{name}");
            assert_eq!(metric.description, *description, "{name}");
            match kind {
                Counter => assert!(!snapshot.counter_points(name).is_empty(), "{name}"),
                Gauge => assert!(!snapshot.gauge_points(name).is_empty(), "{name}"),
                Histogram(bounds) => {
                    for point in snapshot.histogram_points(name).values() {
                        assert_eq!(point.bounds, *bounds, "{name}");
                        assert_eq!(point.bucket_counts.len(), bounds.len() + 1, "{name}");
                    }
                }
            }
        }
    }

    /// Returns the metric name for the sealed memory request `variant`.
    fn request(variant: sealed_memory_request::Request) -> RequestMetricName {
        RequestMetricName::new_sealed_memory_request(&variant)
    }

    /// Returns the metric name for an `AddMemoryRequest`.
    fn add_memory() -> RequestMetricName {
        request(sealed_memory_request::Request::AddMemoryRequest(AddMemoryRequest::default()))
    }

    #[test]
    fn request_metric_name_attribute_values() {
        use sealed_memory_request::Request as R;
        #[allow(deprecated)]
        let cases: Vec<(RequestMetricName, &str)> = vec![
            (RequestMetricName::total(), "total"),
            (RequestMetricName::handshake(), "Handshake"),
            (RequestMetricName::decryption_failure(), "DecryptionFailure"),
            (RequestMetricName::deserialization_failure(), "DeserializationFailure"),
            (RequestMetricName::empty_tls_frame(), "EmptyTlsFrame"),
            (RequestMetricName::empty_request(), "EmptyRequest"),
            (RequestMetricName::session_start(), "SessionStart"),
            (request(R::UserRegistrationRequest(Default::default())), "UserRegistrationRequest"),
            (request(R::KeySyncRequest(Default::default())), "KeySyncRequest"),
            (request(R::AddMemoryRequest(Default::default())), "AddMemoryRequest"),
            (request(R::AddMemoriesRequest(Default::default())), "AddMemoriesRequest"),
            (request(R::GetMemoriesRequest(Default::default())), "GetMemoriesRequest"),
            (request(R::ResetMemoryRequest(Default::default())), "ResetMemoryRequest"),
            (request(R::GetMemoryByIdRequest(Default::default())), "GetMemoryByIdRequest"),
            (request(R::GetMemoryByNameRequest(Default::default())), "GetMemoryByNameRequest"),
            (request(R::DeleteMemoryRequest(Default::default())), "DeleteMemoryRequest"),
            (request(R::GetMemoriesByIdRequest(Default::default())), "GetMemoriesByIdRequest"),
            (request(R::SearchMemoriesRequest(Default::default())), "SearchMemoriesRequest"),
            (
                request(R::GetDatabaseMetricsRequest(Default::default())),
                "GetDatabaseMetricsRequest",
            ),
            (request(R::SyncDatabaseRequest(Default::default())), "SyncDatabaseRequest"),
        ];

        let harness = test_metrics();
        for (name, expected) in &cases {
            assert_eq!(Value::from(name.clone()).as_str(), *expected);
            harness.metrics.inc_requests(name.clone());
        }

        // Every name maps to a distinct `request_type` series.
        let snapshot = harness.collect();
        let expected: BTreeMap<Attrs, u64> = cases
            .iter()
            .map(|(_, request_type)| (attrs(&[("request_type", request_type)]), 1))
            .collect();
        assert_eq!(expected.len(), cases.len());
        assert_eq!(snapshot.counter_points("rpc_count"), &expected);
    }

    #[test]
    fn inc_requests_counts_per_request_type() {
        let harness = test_metrics();
        let metrics = &harness.metrics;
        let before = harness.collect();
        metrics.inc_requests(RequestMetricName::total());
        metrics.inc_requests(RequestMetricName::total());
        metrics.inc_requests(RequestMetricName::handshake());
        metrics.inc_requests(add_memory());
        metrics.inc_requests(add_memory());
        metrics.inc_requests(add_memory());

        let snapshot = harness.collect();
        assert_eq!(
            snapshot.counter_points("rpc_count"),
            &BTreeMap::from([
                (attrs(&[("request_type", "total")]), 2),
                (attrs(&[("request_type", "SessionStart")]), 0),
                (attrs(&[("request_type", "Handshake")]), 1),
                (attrs(&[("request_type", "AddMemoryRequest")]), 3),
            ])
        );
        // `inc_requests` does not touch failures.
        assert_eq!(snapshot.counter_increments(&before, "rpc_failure_count"), BTreeMap::new());
    }

    #[test]
    fn record_failure_counts_request_type_and_total_once() {
        let harness = test_metrics();
        let metrics = &harness.metrics;
        let before = harness.collect();
        metrics.record_failure(add_memory(), tonic::Code::FailedPrecondition);
        metrics.record_failure(add_memory(), tonic::Code::FailedPrecondition);
        metrics.record_failure(add_memory(), tonic::Code::Internal);
        metrics.record_failure(RequestMetricName::handshake(), tonic::Code::Internal);
        metrics
            .record_failure(RequestMetricName::decryption_failure(), tonic::Code::InvalidArgument);

        let snapshot = harness.collect();
        assert_eq!(
            snapshot.counter_increments(&before, "rpc_failure_count"),
            BTreeMap::from([
                (failure_series("AddMemoryRequest", "FAILED_PRECONDITION"), 2),
                (failure_series("AddMemoryRequest", "INTERNAL"), 1),
                (failure_series("Handshake", "INTERNAL"), 1),
                (failure_series("DecryptionFailure", "INVALID_ARGUMENT"), 1),
                (failure_series("total", "FAILED_PRECONDITION"), 2),
                (failure_series("total", "INTERNAL"), 2),
                (failure_series("total", "INVALID_ARGUMENT"), 1),
            ])
        );
        // `record_failure` does not touch the request count.
        assert_eq!(snapshot.counter_increments(&before, "rpc_count"), BTreeMap::new());
    }

    #[test]
    fn record_failure_records_unattributed_failures_once() {
        let harness = test_metrics();
        let before = harness.collect();
        harness.metrics.record_failure(RequestMetricName::total(), tonic::Code::Internal);
        assert_eq!(
            harness.collect().counter_increments(&before, "rpc_failure_count"),
            BTreeMap::from([(failure_series("total", "INTERNAL"), 1)])
        );
    }

    #[test]
    fn record_failure_does_not_mirror_session_start_into_total() {
        let harness = test_metrics();
        let before = harness.collect();
        harness
            .metrics
            .record_failure(RequestMetricName::session_start(), tonic::Code::ResourceExhausted);
        assert_eq!(
            harness.collect().counter_increments(&before, "rpc_failure_count"),
            BTreeMap::from([(failure_series("SessionStart", "RESOURCE_EXHAUSTED"), 1)])
        );
    }

    /// The `status_code` label of every gRPC status code, indexed by code
    /// number as in google/rpc/code.proto.
    const STATUS_CODE_LABELS: [&str; 17] = [
        "OK",
        "CANCELLED",
        "UNKNOWN",
        "INVALID_ARGUMENT",
        "DEADLINE_EXCEEDED",
        "NOT_FOUND",
        "ALREADY_EXISTS",
        "PERMISSION_DENIED",
        "RESOURCE_EXHAUSTED",
        "FAILED_PRECONDITION",
        "ABORTED",
        "OUT_OF_RANGE",
        "UNIMPLEMENTED",
        "INTERNAL",
        "UNAVAILABLE",
        "DATA_LOSS",
        "UNAUTHENTICATED",
    ];

    #[test]
    fn record_failure_labels_canonical_status_codes() {
        let harness = test_metrics();
        let before = harness.collect();
        for (number, label) in (0..).zip(STATUS_CODE_LABELS) {
            let code = tonic::Code::from(number);
            // `Code::from` maps unknown numbers to `Unknown`.
            assert_eq!(code as i32, number, "{label}");
            assert_eq!(status_code_label(code), label, "{code:?}");
            harness.metrics.record_failure(RequestMetricName::total(), code);
        }

        let expected: BTreeMap<Attrs, u64> =
            STATUS_CODE_LABELS.iter().map(|label| (failure_series("total", label), 1)).collect();
        assert_eq!(harness.collect().counter_increments(&before, "rpc_failure_count"), expected);
    }

    /// The host derives the streamz columns of `rpc_failure_count` from a
    /// single exported point, so all points must have the same attributes.
    #[test]
    fn every_failure_point_has_request_type_and_status_code() {
        let harness = test_metrics();
        for name in RequestMetricName::failable() {
            for (number, _) in (0..).zip(STATUS_CODE_LABELS) {
                harness.metrics.record_failure(name.clone(), tonic::Code::from(number));
            }
        }

        let snapshot = harness.collect();
        let points = snapshot.counter_points("rpc_failure_count");
        assert_eq!(points.len(), FAILABLE_REQUEST_TYPES.len() * STATUS_CODE_LABELS.len());
        for series in points.keys() {
            let keys: Vec<&str> = series.iter().map(|(key, _)| key.as_str()).collect();
            assert_eq!(keys, ["request_type", "status_code"], "{series:?}");
        }
    }

    #[test]
    fn record_latency_records_request_type_and_total() {
        let harness = test_metrics();
        let metrics = &harness.metrics;
        // Zero is rounded up to 1 ms.
        metrics.record_latency(0, RequestMetricName::handshake());
        metrics.record_latency(30, add_memory());
        metrics.record_latency(15_000, add_memory());

        let snapshot = harness.collect();
        let points = snapshot.histogram_points("rpc_latency");
        assert_eq!(points.len(), 4, "{points:?}");

        let handshake = snapshot.histogram("rpc_latency", &[("request_type", "Handshake")]);
        assert_eq!((handshake.count, handshake.sum), (1, 1));
        assert_eq!(handshake.nonzero_buckets(), vec![(5., 1)]);

        let add = snapshot.histogram("rpc_latency", &[("request_type", "AddMemoryRequest")]);
        assert_eq!((add.count, add.sum), (2, 15_030));
        assert_eq!(add.nonzero_buckets(), vec![(50., 1), (20_000., 1)]);

        let total = snapshot.histogram("rpc_latency", &[("request_type", "total")]);
        assert_eq!((total.count, total.sum), (3, 15_031));
        assert_eq!(total.nonzero_buckets(), vec![(5., 1), (50., 1), (20_000., 1)]);

        // The synthetic startup series is untouched.
        let test = snapshot.histogram("rpc_latency", &[("request_type", "test")]);
        assert_eq!((test.count, test.sum), (1, 1));
    }

    #[test]
    fn record_latency_with_total_name_records_total_once() {
        let harness = test_metrics();
        harness.metrics.record_latency(10, RequestMetricName::total());
        let snapshot = harness.collect();
        let total = snapshot.histogram("rpc_latency", &[("request_type", "total")]);
        assert_eq!((total.count, total.sum), (1, 10));
        // Besides the startup `test` series, only `total` is recorded.
        assert_eq!(snapshot.histogram_points("rpc_latency").len(), 2);
    }

    #[test]
    fn db_size_uses_explicit_byte_buckets() {
        let harness = test_metrics();
        for size in [0, 1, MB, MB + 1, 50 * MB, 60 * MB, 500 * MB, 600 * MB] {
            harness.metrics.record_db_size(size as u64);
        }

        let snapshot = harness.collect();
        let point = snapshot.histogram("db_size", &[]);
        assert_eq!(point.count, 8);
        assert_eq!(point.sum, (1 + MB + MB + 1 + 50 * MB + 60 * MB + 500 * MB + 600 * MB) as u64);
        assert_eq!(
            point.nonzero_buckets(),
            vec![
                (0., 1),
                (MB as f64, 2),
                ((5 * MB) as f64, 1),
                ((50 * MB) as f64, 1),
                ((75 * MB) as f64, 1),
                ((500 * MB) as f64, 1),
                (INF, 1),
            ]
        );
    }

    #[test]
    fn db_init_latency_is_labelled_by_db_size_bucket() {
        let harness = test_metrics();
        harness.metrics.record_db_init_latency(1_500, bucket_db_size(15 * MB));
        harness.metrics.record_db_init_latency(40_000, bucket_db_size(200 * MB));

        let snapshot = harness.collect();
        assert_eq!(snapshot.histogram_points("db_init_latency").len(), 3);

        let mid = snapshot.histogram("db_init_latency", &[("db_size_bucket", "10MB-20MB")]);
        assert_eq!((mid.count, mid.sum), (1, 1_500));
        assert_eq!(mid.nonzero_buckets(), vec![(2_500., 1)]);

        let large = snapshot.histogram("db_init_latency", &[("db_size_bucket", "100MB+")]);
        assert_eq!((large.count, large.sum), (1, 40_000));
        assert_eq!(large.nonzero_buckets(), vec![(60_000., 1)]);

        // The startup sample is in its own series, not in a real size bucket.
        let startup = snapshot.histogram("db_init_latency", &[("db_size_bucket", "test")]);
        assert_eq!((startup.count, startup.sum), (1, 1));
    }

    #[test]
    fn latency_histograms_record_into_ms_buckets() {
        // One sample per interesting edge of `LATENCY_MS_BOUNDARIES` (upper
        // bounds are inclusive): 0 and 5 land on a boundary, 6 is just past
        // one, 7_500 is a mid-range boundary, 15_000 falls in the added slow
        // tail, 120_000 is the last boundary and 120_001 overflows to `INF`.
        let values = [0, 5, 6, 7_500, 15_000, 120_000, 120_001];
        for (name, record) in LATENCY_HISTOGRAMS {
            let harness = test_metrics();
            for value in values {
                record(&harness.metrics, value);
            }
            let snapshot = harness.collect();
            assert_eq!(snapshot.histogram_points(name).len(), 1, "{name}");
            let point = snapshot.histogram(name, &[]);
            assert_eq!(point.count, values.len() as u64, "{name}");
            assert_eq!(point.sum, values.iter().sum::<u64>(), "{name}");
            // `nonzero_buckets` lists only buckets that received a sample, so
            // the jumps below (e.g. 10 -> 7_500) skip empty buckets.
            assert_eq!(
                point.nonzero_buckets(),
                vec![
                    (0., 1),
                    (5., 1),
                    (10., 1),
                    (7_500., 1),
                    (20_000., 1),
                    (120_000., 1),
                    (INF, 1),
                ],
                "{name}"
            );
        }
    }

    #[test]
    fn count_histograms_record_into_count_buckets() {
        let values = [0, 1, 2, 3, 4, 10, 11, 10_000, 10_001];
        for (name, record) in COUNT_HISTOGRAMS {
            let harness = test_metrics();
            for value in values {
                record(&harness.metrics, value);
            }
            let snapshot = harness.collect();
            let point = snapshot.histogram(name, &[]);
            assert_eq!(point.count, values.len() as u64, "{name}");
            assert_eq!(point.sum, values.iter().sum::<u64>(), "{name}");
            assert_eq!(
                point.nonzero_buckets(),
                vec![
                    (0., 1),
                    (1., 1),
                    (2., 1),
                    (3., 1),
                    (5., 1),
                    (10., 1),
                    (25., 1),
                    (10_000., 1),
                    (INF, 1),
                ],
                "{name}"
            );
        }
    }

    #[test]
    fn speed_histograms_round_up_and_record_into_speed_buckets() {
        for (name, record) in SPEED_HISTOGRAMS {
            let harness = test_metrics();
            // Zero is rounded up to 1.
            for value in [0, 1, 4, 10_001] {
                record(&harness.metrics, value);
            }
            let snapshot = harness.collect();
            assert_eq!(snapshot.histogram_points(name).len(), 1, "{name}");
            let point = snapshot.histogram(name, &[]);
            assert_eq!((point.count, point.sum), (4, 1 + 1 + 4 + 10_001), "{name}");
            assert_eq!(point.nonzero_buckets(), vec![(1., 2), (5., 1), (INF, 1)], "{name}");
        }
    }

    #[test]
    fn unit_counters_increment_by_one() {
        for (name, inc) in UNIT_COUNTERS {
            let harness = test_metrics();
            for _ in 0..3 {
                inc(&harness.metrics);
            }
            let snapshot = harness.collect();
            assert_eq!(snapshot.counter_points(name), &BTreeMap::from([(attrs(&[]), 3)]), "{name}");
            // No other counter moves.
            for (other, _) in UNIT_COUNTERS.iter().filter(|(metric_name, _)| metric_name != name) {
                assert_eq!(snapshot.counter(other, &[]), 0, "{name} moved {other}");
            }
            for (other, _) in AMOUNT_COUNTERS {
                assert_eq!(snapshot.counter(other, &[]), 0, "{name} moved {other}");
            }
        }
    }

    #[test]
    fn amount_counters_increment_by_amount() {
        for (name, inc) in AMOUNT_COUNTERS {
            let harness = test_metrics();
            inc(&harness.metrics, 0);
            assert_eq!(harness.collect().counter(name, &[]), 0, "{name}");
            inc(&harness.metrics, 2);
            inc(&harness.metrics, 5);
            let snapshot = harness.collect();
            assert_eq!(snapshot.counter_points(name), &BTreeMap::from([(attrs(&[]), 7)]), "{name}");
            for (other, _) in AMOUNT_COUNTERS.iter().filter(|(metric_name, _)| metric_name != name)
            {
                assert_eq!(snapshot.counter(other, &[]), 0, "{name} moved {other}");
            }
            for (other, _) in UNIT_COUNTERS {
                assert_eq!(snapshot.counter(other, &[]), 0, "{name} moved {other}");
            }
        }
    }

    #[test]
    fn inc_session_rejected_counts_reason_and_legacy_low_memory_counter() {
        let harness = test_metrics();
        let before = harness.collect();
        harness.metrics.inc_session_rejected(SessionRejectReason::MaxSessions);
        harness.metrics.inc_session_rejected(SessionRejectReason::MapCount);
        harness.metrics.inc_session_rejected(SessionRejectReason::LowMemory);
        harness.metrics.inc_session_rejected(SessionRejectReason::LowMemory);

        let snapshot = harness.collect();
        assert_eq!(
            snapshot.counter_increments(&before, "session_rejected"),
            BTreeMap::from([
                (attrs(&[("reason", "max_sessions")]), 1),
                (attrs(&[("reason", "map_count")]), 1),
                (attrs(&[("reason", "low_memory")]), 2),
            ])
        );
        // Only low-memory rejections also move the legacy counter.
        assert_eq!(snapshot.counter("session_rejected_low_memory", &[]), 2);
    }

    #[test]
    fn admission_gauges_record_last_value() {
        let gauges: [(&str, RecordFn); 3] = [
            ("active_sessions", Metrics::record_active_sessions),
            ("max_active_sessions", Metrics::record_max_active_sessions),
            ("process_map_count", Metrics::record_process_map_count),
        ];
        for (name, record) in gauges {
            let harness = test_metrics();
            for value in [5, 3, 0] {
                record(&harness.metrics, value);
                assert_eq!(
                    harness.collect().gauge_points(name),
                    &BTreeMap::from([(attrs(&[]), value)]),
                    "{name}"
                );
            }
        }
    }

    #[test]
    fn db_persist_queue_size_gauge_records_last_value() {
        let harness = test_metrics();
        harness.metrics.record_db_persist_queue_size(5);
        assert_eq!(
            harness.collect().gauge_points("db_persist_queue_size"),
            &BTreeMap::from([(attrs(&[]), 5)])
        );
        harness.metrics.record_db_persist_queue_size(3);
        assert_eq!(
            harness.collect().gauge_points("db_persist_queue_size"),
            &BTreeMap::from([(attrs(&[]), 3)])
        );
        harness.metrics.record_db_persist_queue_size(0);
        assert_eq!(
            harness.collect().gauge_points("db_persist_queue_size"),
            &BTreeMap::from([(attrs(&[]), 0)])
        );
    }

    #[test]
    fn db_persist_queue_size_counts_enqueues_until_the_worker_reads_the_queue() {
        let harness = test_metrics();
        let queue_size = || harness.collect().gauge("db_persist_queue_size", &[]);
        harness.metrics.inc_db_persist_queue_size();
        assert_eq!(queue_size(), 1);
        harness.metrics.inc_db_persist_queue_size();
        harness.metrics.inc_db_persist_queue_size();
        assert_eq!(queue_size(), 3);
        harness.metrics.dec_db_persist_queue_size();
        assert_eq!(queue_size(), 2);
        // The worker's reading replaces the count...
        harness.metrics.record_db_persist_queue_size(0);
        assert_eq!(queue_size(), 0);
        // ...which keeps counting from there, and never goes below zero.
        harness.metrics.dec_db_persist_queue_size();
        assert_eq!(queue_size(), 0);
        harness.metrics.inc_db_persist_queue_size();
        assert_eq!(queue_size(), 1);
    }

    #[test]
    fn transfer_speed_is_kb_per_ms_with_at_least_1_ms() {
        use std::time::Duration;
        assert_eq!(transfer_speed_kb_per_ms(10 * MB, Duration::from_millis(10)), 1024);
        assert_eq!(transfer_speed_kb_per_ms(10 * MB, Duration::from_secs(10)), 1);
        // Sub-millisecond transfers count as taking 1 ms.
        assert_eq!(transfer_speed_kb_per_ms(4 * KB, Duration::ZERO), 4);
        assert_eq!(transfer_speed_kb_per_ms(4 * KB, Duration::from_micros(999)), 4);
        // Rounds down, so slow transfers are 0 (which `record_db_*_speed`
        // records as 1).
        assert_eq!(transfer_speed_kb_per_ms(KB - 1, Duration::from_millis(1)), 0);
        assert_eq!(transfer_speed_kb_per_ms(4 * KB, Duration::from_millis(5)), 0);
    }

    fn init_result(code: Option<i32>) -> icing::InitializeResultProto {
        icing::InitializeResultProto {
            status: Some(icing::StatusProto { code, message: None }),
            ..Default::default()
        }
    }

    #[test]
    fn icing_init_status_maps_status_codes() {
        let harness = test_metrics();
        let metrics = &harness.metrics;
        metrics.record_icing_initialization_stats(&init_result(Some(
            icing::status_proto::Code::Ok as i32,
        )));
        metrics.record_icing_initialization_stats(&init_result(Some(
            icing::status_proto::Code::WarningDataLoss as i32,
        )));
        metrics.record_icing_initialization_stats(&init_result(Some(
            icing::status_proto::Code::Internal as i32,
        )));
        // Missing status, missing code, and an unknown code all map to
        // UNKNOWN (the first two via the proto default value 0 = UNKNOWN).
        metrics.record_icing_initialization_stats(&icing::InitializeResultProto::default());
        metrics.record_icing_initialization_stats(&init_result(None));
        metrics.record_icing_initialization_stats(&init_result(Some(999)));

        let snapshot = harness.collect();
        assert_eq!(
            snapshot.counter_points("icing_init_status"),
            &BTreeMap::from([
                (attrs(&[("status_code", "OK")]), 1),
                (attrs(&[("status_code", "WARNING_DATA_LOSS")]), 1),
                (attrs(&[("status_code", "INTERNAL")]), 1),
                (attrs(&[("status_code", "UNKNOWN")]), 3),
            ])
        );
        // Without `initialize_stats`, nothing else is recorded.
        for name in [
            "icing_init_latency_ms",
            "icing_recovery_cause",
            "icing_recovery_latency_ms",
            "icing_num_previous_init_failures",
            "icing_num_failed_reindexed_documents",
        ] {
            assert!(!snapshot.names().contains(name), "{name}");
        }
    }

    #[test]
    fn icing_initialization_stats_map_to_metrics() {
        let harness = test_metrics();
        let mut result = init_result(Some(icing::status_proto::Code::Ok as i32));
        result.initialize_stats = Some(icing::InitializeStatsProto {
            latency_ms: Some(150),
            document_store_recovery_cause: Some(1),
            index_restoration_cause: Some(2),
            schema_store_recovery_cause: Some(3),
            integer_index_restoration_cause: Some(4),
            qualified_id_join_index_restoration_cause: Some(0),
            embedding_index_restoration_cause: Some(999),
            document_store_recovery_latency_ms: Some(50),
            index_restoration_latency_ms: Some(25),
            schema_store_recovery_latency_ms: Some(15_000),
            num_previous_init_failures: Some(2),
            num_failed_reindexed_documents: Some(10),
            ..Default::default()
        });
        harness.metrics.record_icing_initialization_stats(&result);

        let snapshot = harness.collect();
        assert_eq!(snapshot.counter("icing_init_status", &[("status_code", "OK")]), 1);

        let init_latency = snapshot.histogram("icing_init_latency_ms", &[]);
        assert_eq!((init_latency.count, init_latency.sum), (1, 150));
        assert_eq!(init_latency.nonzero_buckets(), vec![(250., 1)]);

        let cause = |component: &str, cause: &str| {
            (attrs(&[("component", component), ("cause", cause)]), 1)
        };
        // TODO: b/571198870 - a NONE cause (no recovery) is counted too, so
        // every healthy init increments `icing_recovery_cause` per component.
        // Left until Gerrit change 52200, which also changes the icing
        // metrics, lands.
        assert_eq!(
            snapshot.counter_points("icing_recovery_cause"),
            &BTreeMap::from([
                cause("document_store", "DATA_LOSS"),
                cause("index", "INCONSISTENT_WITH_GROUND_TRUTH"),
                cause("schema_store", "SCHEMA_CHANGES_OUT_OF_SYNC"),
                cause("integer_index", "IO_ERROR"),
                cause("qualified_id_join_index", "NONE"),
                cause("embedding_index", "UNKNOWN"),
            ])
        );

        let recovery = snapshot.histogram_points("icing_recovery_latency_ms");
        assert_eq!(recovery.len(), 3, "{recovery:?}");
        for (component, latency, upper) in
            [("document_store", 50, 50.), ("index", 25, 25.), ("schema_store", 15_000, INF)]
        {
            let point =
                snapshot.histogram("icing_recovery_latency_ms", &[("component", component)]);
            assert_eq!((point.count, point.sum), (1, latency), "{component}");
            assert_eq!(point.nonzero_buckets(), vec![(upper, 1)], "{component}");
        }

        let failures = snapshot.histogram("icing_num_previous_init_failures", &[]);
        assert_eq!((failures.count, failures.sum), (1, 2));
        assert_eq!(failures.nonzero_buckets(), vec![(5., 1)]);

        let reindexed = snapshot.histogram("icing_num_failed_reindexed_documents", &[]);
        assert_eq!((reindexed.count, reindexed.sum), (1, 10));
        assert_eq!(reindexed.nonzero_buckets(), vec![(10., 1)]);
    }

    #[test]
    fn icing_initialization_stats_skip_unset_fields() {
        let harness = test_metrics();
        let mut result = init_result(Some(icing::status_proto::Code::Ok as i32));
        result.initialize_stats =
            Some(icing::InitializeStatsProto { latency_ms: Some(7), ..Default::default() });
        harness.metrics.record_icing_initialization_stats(&result);

        let snapshot = harness.collect();
        let init_latency = snapshot.histogram("icing_init_latency_ms", &[]);
        assert_eq!((init_latency.count, init_latency.sum), (1, 7));
        for name in [
            "icing_recovery_cause",
            "icing_recovery_latency_ms",
            "icing_num_previous_init_failures",
            "icing_num_failed_reindexed_documents",
        ] {
            assert!(!snapshot.names().contains(name), "{name}");
        }
    }

    #[test]
    fn inc_dek_rotation_count_counts_each_response_type() {
        assert_eq!(
            DekRotationResponseType::ALL.map(|response_type| response_type.as_str()),
            ["ok", "retry_error", "unauthenticated", "internal_error", "invalid_argument"]
        );
        let harness = test_metrics();
        for (i, response_type) in DekRotationResponseType::ALL.into_iter().enumerate() {
            for _ in 0..=i {
                harness.metrics.inc_dek_rotation_count(response_type);
            }
        }

        let snapshot = harness.collect();
        for (i, response_type) in DekRotationResponseType::ALL.into_iter().enumerate() {
            assert_eq!(
                snapshot
                    .counter("dek_rotation_count", &[("response_type", response_type.as_str())]),
                i as u64 + 1,
                "{response_type:?}"
            );
        }
    }

    #[test]
    fn record_dek_rotation_run_records_successful_run() {
        let harness = test_metrics();
        let mb = MB as u64;
        harness.metrics.record_dek_rotation_run(
            DekRotationRun::Succeeded { blobs: 12, ciphertext_bytes: 2 * mb },
            500,
        );

        let snapshot = harness.collect();
        assert_eq!(snapshot.counter("dek_rotation_blobs_reencrypted_total", &[]), 12);
        assert_eq!(snapshot.counter("dek_rotation_bytes_reencrypted_total", &[]), 2 * mb);
        let blobs = snapshot.histogram("dek_rotation_blobs_per_run", &[]);
        assert_eq!((blobs.count, blobs.sum), (1, 12));
        let bytes = snapshot.histogram("dek_rotation_bytes_per_run", &[]);
        assert_eq!((bytes.count, bytes.sum), (1, 2 * mb));
        let throughput = snapshot.histogram("dek_rotation_throughput_bytes_per_sec", &[]);
        assert_eq!((throughput.count, throughput.sum), (1, 4 * mb));
        let latency = snapshot.histogram(
            "dek_rotation_latency_ms",
            &[("status", "success"), ("bytes_tier", "1-10MB"), ("blobs_tier", "10-50")],
        );
        assert_eq!((latency.count, latency.sum), (1, 500));
    }

    #[test]
    fn record_dek_rotation_run_adds_up_totals_across_runs() {
        let harness = test_metrics();
        harness.metrics.record_dek_rotation_run(
            DekRotationRun::Succeeded { blobs: 3, ciphertext_bytes: 300 },
            10,
        );
        harness.metrics.record_dek_rotation_run(
            DekRotationRun::Succeeded { blobs: 4, ciphertext_bytes: 400 },
            20,
        );

        let snapshot = harness.collect();
        assert_eq!(snapshot.counter("dek_rotation_blobs_reencrypted_total", &[]), 7);
        assert_eq!(snapshot.counter("dek_rotation_bytes_reencrypted_total", &[]), 700);
        let blobs = snapshot.histogram("dek_rotation_blobs_per_run", &[]);
        assert_eq!((blobs.count, blobs.sum), (2, 7));
        let bytes = snapshot.histogram("dek_rotation_bytes_per_run", &[]);
        assert_eq!((bytes.count, bytes.sum), (2, 700));
        let throughput = snapshot.histogram("dek_rotation_throughput_bytes_per_sec", &[]);
        assert_eq!((throughput.count, throughput.sum), (2, 30_000 + 20_000));
        let latency = snapshot.histogram(
            "dek_rotation_latency_ms",
            &[("status", "success"), ("bytes_tier", "<1MB"), ("blobs_tier", "<10")],
        );
        assert_eq!((latency.count, latency.sum), (2, 30));
    }

    #[test]
    fn record_dek_rotation_run_counts_a_zero_ms_run_as_one_ms() {
        let harness = test_metrics();
        harness.metrics.record_dek_rotation_run(
            DekRotationRun::Succeeded { blobs: 1, ciphertext_bytes: 10 },
            0,
        );

        let snapshot = harness.collect();
        let throughput = snapshot.histogram("dek_rotation_throughput_bytes_per_sec", &[]);
        assert_eq!((throughput.count, throughput.sum), (1, 10_000));
        let latency = snapshot.histogram(
            "dek_rotation_latency_ms",
            &[("status", "success"), ("bytes_tier", "<1MB"), ("blobs_tier", "<10")],
        );
        assert_eq!((latency.count, latency.sum), (1, 1));
    }

    #[test]
    fn record_dek_rotation_run_saturates_throughput() {
        let harness = test_metrics();
        harness.metrics.record_dek_rotation_run(
            DekRotationRun::Succeeded { blobs: 1, ciphertext_bytes: u64::MAX / 2 },
            1,
        );

        let snapshot = harness.collect();
        let throughput = snapshot.histogram("dek_rotation_throughput_bytes_per_sec", &[]);
        assert_eq!((throughput.count, throughput.sum), (1, u64::MAX));
    }

    #[test]
    fn record_dek_rotation_run_records_only_latency_for_failed_run() {
        let harness = test_metrics();
        harness.metrics.record_dek_rotation_run(DekRotationRun::Failed, 0);

        let snapshot = harness.collect();
        assert_eq!(snapshot.counter("dek_rotation_blobs_reencrypted_total", &[]), 0);
        assert_eq!(snapshot.counter("dek_rotation_bytes_reencrypted_total", &[]), 0);
        for name in [
            "dek_rotation_blobs_per_run",
            "dek_rotation_bytes_per_run",
            "dek_rotation_throughput_bytes_per_sec",
        ] {
            assert!(!snapshot.names().contains(name), "{name}");
        }
        let latency = snapshot.histogram(
            "dek_rotation_latency_ms",
            &[("status", "failure"), ("bytes_tier", "unknown"), ("blobs_tier", "unknown")],
        );
        assert_eq!((latency.count, latency.sum), (1, 1));
    }

    #[test]
    fn bucket_db_size_labels() {
        let cases = [
            (0, "0-100KB"),
            (100 * KB, "0-100KB"),
            (100 * KB + 1, "100KB-10MB"),
            (10 * MB, "100KB-10MB"),
            (10 * MB + 1, "10MB-20MB"),
            (20 * MB, "10MB-20MB"),
            (20 * MB + 1, "20MB-30MB"),
            (35 * MB, "30MB-40MB"),
            (45 * MB, "40MB-50MB"),
            (55 * MB, "50MB-60MB"),
            (65 * MB, "60MB-70MB"),
            (75 * MB, "70MB-80MB"),
            (85 * MB, "80MB-90MB"),
            (100 * MB, "90MB-100MB"),
            (100 * MB + 1, "100MB+"),
        ];
        for (size, expected) in cases {
            assert_eq!(bucket_db_size(size), expected, "{size}");
        }
    }

    #[test]
    fn db_persist_lock_metrics_record_conflicts_and_wait_latency() {
        let harness = test_metrics();
        let metrics = &harness.metrics;
        metrics.inc_db_persist_lock_conflicts();
        metrics.inc_db_persist_lock_conflicts();
        metrics.record_db_persist_lock_wait_latency(250);
        metrics.record_db_persist_lock_wait_latency(2_500);

        let snapshot = harness.collect();
        assert_eq!(snapshot.counter("db_persist_lock_conflict_count", &[]), 2);
        let wait = snapshot.histogram("db_persist_lock_wait_latency", &[]);
        assert_eq!((wait.count, wait.sum), (2, 2_750));
        assert_eq!(wait.nonzero_buckets(), vec![(250., 1), (2_500., 1)]);
    }
}
