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
use std::sync::Arc;

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
    // Latency of each RPC.
    rpc_latency: Histogram<u64>,
    // Size of the database in bytes.
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
    // Number of failures when syncing keys.
    decrypt_dek_failures: Counter<u64>,
    // Number of failures when deserializing database.
    user_info_deserialization_failures: Counter<u64>,
    // Number of failures when decrypting database.
    db_decryption_failures: Counter<u64>,
    // Queue size of the in the database persist queue.
    db_persist_queue_size: Gauge<u64>,
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

    // Icing initialization stats
    icing_init_status: Counter<u64>,
    icing_init_latency_ms: Histogram<u64>,

    // Recovery stats (labelled by component)
    icing_recovery_cause: Counter<u64>,
    icing_recovery_latency_ms: Histogram<u64>,

    // Failure counting distributions
    icing_num_previous_init_failures: Histogram<u64>,
    icing_num_failed_reindexed_documents: Histogram<u64>,
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
            .with_description("Latency in ms of each RPC.")
            .with_unit("ms")
            .with_boundaries(LATENCY_MS_BOUNDARIES.to_vec())
            .build();
        let db_size = meter
            .u64_histogram("db_size")
            .with_description("Size of the database in bytes.")
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
        rpc_latency.record(1, &[KeyValue::new("request_type", "test")]);
        db_size.record(1, &[]);
        db_init_latency.record(1, &[KeyValue::new("db_size_bucket", "0-100KB")]);
        db_cleanup_latency.record(0, &[]);
        db_cleanup_count.record(0, &[]);
        db_persist_latency.record(1, &[]);
        db_persist_latency_with_retries.record(1, &[]);
        db_persist_attempts.record(1, &[]);
        db_connect_retries.add(0, &[]);
        db_persist_failures.add(0, &[]);
        decrypt_dek_failures.add(0, &[]);
        user_info_deserialization_failures.add(0, &[]);
        db_decryption_failures.add(0, &[]);
        db_persist_queue_size.record(0, &[]);
        db_optimize_latency.record(1, &[]);
        key_sync_db_fetch_latency.record(0, &[]);
        key_sync_decrypt_latency.record(0, &[]);
        db_rebase_operation_failures.add(0, &[]);
        db_cleanup_failures.add(0, &[]);
        tls_handshake_failures.add(0, &[]);
        tls_receive_failures.add(0, &[]);
        persistence_enqueue_failures.add(0, &[]);
        let orphaned_blob_deletes = meter
            .u64_counter("orphaned_blob_deletes")
            .with_description("Number of blobs that should have been soft-deleted but were not.")
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
        let session_rejected_low_memory = meter
            .u64_counter("session_rejected_low_memory")
            .with_description("Number of sessions rejected due to low memory.")
            .build();
        session_rejected_low_memory.add(0, &[]);

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
            decrypt_dek_failures,
            user_info_deserialization_failures,
            db_decryption_failures,
            db_persist_queue_size,
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
            icing_init_status,
            icing_init_latency_ms,
            icing_recovery_cause,
            icing_recovery_latency_ms,
            icing_num_previous_init_failures,
            icing_num_failed_reindexed_documents,
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
    /// Calling this function will automatically record  latency for the "total"
    /// requests group as well.
    pub fn record_latency(&self, elapsed_time_ms: u64, name: RequestMetricName) {
        // Round up as 1ms.
        let elapsed_time_ms = std::cmp::max(1, elapsed_time_ms);

        self.rpc_latency.record(elapsed_time_ms, &[KeyValue::new("request_type", name)]);
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

    pub fn inc_decrypt_dek_failures(&self) {
        self.decrypt_dek_failures.add(1, &[]);
    }

    pub fn inc_user_info_deserialization_failures(&self) {
        self.user_info_deserialization_failures.add(1, &[]);
    }

    pub fn inc_db_decryption_failures(&self) {
        self.db_decryption_failures.add(1, &[]);
    }

    pub fn record_db_persist_queue_size(&self, max: u64) {
        self.db_persist_queue_size.record(max, &[]);
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

    pub fn inc_session_rejected_low_memory(&self) {
        self.session_rejected_low_memory.add(1, &[]);
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
        ("decrypt_dek_failures", Metrics::inc_decrypt_dek_failures),
        ("user_info_deserialization_failures", Metrics::inc_user_info_deserialization_failures),
        ("db_decryption_failures", Metrics::inc_db_decryption_failures),
        ("db_cleanup_failures", Metrics::inc_db_cleanup_failures),
        ("tls_handshake_failures", Metrics::inc_tls_handshake_failures),
        ("tls_receive_failures", Metrics::inc_tls_receive_failures),
        ("persistence_enqueue_failures", Metrics::inc_persistence_enqueue_failures),
        ("session_rejected_low_memory", Metrics::inc_session_rejected_low_memory),
    ];

    /// Counters that are incremented by a caller-provided amount.
    const AMOUNT_COUNTERS: &[(&str, RecordFn)] = &[
        ("db_rebase_operation_failures", Metrics::inc_db_rebase_operation_failures),
        ("orphaned_blob_deletes", Metrics::inc_orphaned_blob_deletes),
    ];

    /// Attribute-less millisecond latency histograms, with the sample that
    /// `Metrics::new` records into each at startup.
    const LATENCY_HISTOGRAMS: &[(&str, RecordFn, u64)] = &[
        ("db_cleanup_latency", Metrics::record_db_cleanup_latency, 0),
        ("db_persist_latency", Metrics::record_db_persist_latency, 1),
        ("db_persist_latency_with_retries", Metrics::record_db_persist_latency_with_retries, 1),
        ("db_optimize_latency", Metrics::record_db_optimize_latency, 1),
        ("key_sync_db_fetch_latency", Metrics::record_key_sync_db_fetch_latency, 0),
        ("key_sync_decrypt_latency", Metrics::record_key_sync_decrypt_latency, 0),
    ];

    /// Count histograms, with the sample recorded into each at startup.
    const COUNT_HISTOGRAMS: &[(&str, RecordFn, u64)] = &[
        ("db_cleanup_count", Metrics::record_db_cleanup_count, 0),
        ("db_persist_attempts", Metrics::record_db_persist_attempts, 1),
    ];

    /// Speed histograms. These are not zero-initialized at startup.
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

        // The gauge starts at zero.
        assert_eq!(
            snapshot.gauge_points("db_persist_queue_size"),
            &BTreeMap::from([(attrs(empty), 0)])
        );

        // Attribute `(key, value)` pairs, as written in the table below.
        type Pairs<'a> = &'a [(&'a str, &'a str)];

        // Histograms carry a single synthetic sample recorded at startup.
        // TODO: b/571198870 - these synthetic samples (including the
        // `request_type=test` series and a 1-byte database) are exported as
        // real observations and skew the distributions on every restart.
        let startup_histograms: &[(&str, Pairs, u64)] = &[
            ("rpc_latency", &[("request_type", "test")], 1),
            ("db_size", empty, 1),
            ("db_init_latency", &[("db_size_bucket", "0-100KB")], 1),
            ("db_cleanup_latency", empty, 0),
            ("db_cleanup_count", empty, 0),
            ("db_persist_latency", empty, 1),
            ("db_persist_latency_with_retries", empty, 1),
            ("db_persist_attempts", empty, 1),
            ("db_optimize_latency", empty, 1),
            ("key_sync_db_fetch_latency", empty, 0),
            ("key_sync_decrypt_latency", empty, 0),
        ];
        for (name, pairs, sample) in startup_histograms {
            let points = snapshot.histogram_points(name);
            assert_eq!(points.len(), 1, "{name}: {points:?}");
            let point = snapshot.histogram(name, pairs);
            assert_eq!((point.count, point.sum), (1, *sample), "{name}");
        }

        // Instruments that are only exported once recorded.
        let expected: BTreeSet<&str> = ["rpc_count", "rpc_failure_count", "db_persist_queue_size"]
            .into_iter()
            .chain(UNIT_COUNTERS.iter().map(|(metric_name, _)| *metric_name))
            .chain(AMOUNT_COUNTERS.iter().map(|(metric_name, _)| *metric_name))
            .chain(startup_histograms.iter().map(|(metric_name, _, _)| *metric_name))
            .collect();
        assert_eq!(snapshot.names(), expected);
        // TODO: b/571198870 - unlike most other histograms, `db_save_speed`
        // and `db_load_speed` are not zero-initialized at startup, so they are
        // missing until the first save or load.
        for name in [
            "db_save_speed",
            "db_load_speed",
            "icing_init_status",
            "icing_init_latency_ms",
            "icing_recovery_cause",
            "icing_recovery_latency_ms",
            "icing_num_previous_init_failures",
            "icing_num_failed_reindexed_documents",
        ] {
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
        metrics.record_db_save_speed(1);
        metrics.record_db_load_speed(1);
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
            ("rpc_latency", "ms", "Latency in ms of each RPC.", Histogram(LATENCY_MS_BOUNDARIES)),
            (
                "db_size",
                "By",
                "Size of the database in bytes.",
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
                "session_rejected_low_memory",
                "",
                "Number of sessions rejected due to low memory.",
                Counter,
            ),
            ("icing_init_status", "", "Icing init status code.", Counter),
            // TODO: b/571198870 - the icing `*_ms` histograms have no unit and
            // use the OpenTelemetry default boundaries (max finite 10 s).
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
    fn record_latency_with_total_name_double_counts_total() {
        let harness = test_metrics();
        // TODO: b/571198870 - if `record_latency` is called with
        // `RequestMetricName::total()`, the sample is recorded twice in the
        // `total` series. Its only caller (`SealedMemorySessionHandler::handle`)
        // always passes a specific request type, so this doesn't happen in
        // production.
        harness.metrics.record_latency(10, RequestMetricName::total());
        let snapshot = harness.collect();
        let total = snapshot.histogram("rpc_latency", &[("request_type", "total")]);
        assert_eq!((total.count, total.sum), (2, 20));
    }

    #[test]
    fn db_size_uses_explicit_byte_buckets() {
        let harness = test_metrics();
        for size in [0, 1, MB, MB + 1, 50 * MB, 60 * MB, 500 * MB, 600 * MB] {
            harness.metrics.record_db_size(size as u64);
        }

        let snapshot = harness.collect();
        let point = snapshot.histogram("db_size", &[]);
        // Includes the 1-byte sample recorded at startup.
        assert_eq!(point.count, 9);
        assert_eq!(
            point.sum,
            (1 + 1 + MB + MB + 1 + 50 * MB + 60 * MB + 500 * MB + 600 * MB) as u64
        );
        assert_eq!(
            point.nonzero_buckets(),
            vec![
                (0., 1),
                (MB as f64, 3),
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

        let startup = snapshot.histogram("db_init_latency", &[("db_size_bucket", "0-100KB")]);
        assert_eq!((startup.count, startup.sum), (1, 1));
    }

    /// Adds `count` to the bucket with upper bound `upper` in a sorted
    /// `(upper_bound, count)` list, inserting it if needed.
    fn add_to_bucket(buckets: &mut Vec<(f64, u64)>, upper: f64, count: u64) {
        match buckets.iter_mut().find(|(bound, _)| *bound == upper) {
            Some((_, existing)) => *existing += count,
            None => {
                buckets.push((upper, count));
                buckets.sort_by(|left, right| left.0.total_cmp(&right.0));
            }
        }
    }

    #[test]
    fn latency_histograms_record_into_ms_buckets() {
        // One sample per interesting edge of `LATENCY_MS_BOUNDARIES` (upper
        // bounds are inclusive): 0 and 5 land on a boundary, 6 is just past
        // one, 7_500 is a mid-range boundary, 15_000 falls in the added slow
        // tail, 120_000 is the last boundary and 120_001 overflows to `INF`.
        let values = [0, 5, 6, 7_500, 15_000, 120_000, 120_001];
        for (name, record, startup) in LATENCY_HISTOGRAMS {
            let harness = test_metrics();
            for value in values {
                record(&harness.metrics, value);
            }
            let snapshot = harness.collect();
            assert_eq!(snapshot.histogram_points(name).len(), 1, "{name}");
            let point = snapshot.histogram(name, &[]);
            assert_eq!(point.count, values.len() as u64 + 1, "{name}");
            assert_eq!(point.sum, values.iter().sum::<u64>() + startup, "{name}");

            // `nonzero_buckets` lists only buckets that received a sample, so
            // the jumps below (e.g. 10 -> 7_500) skip empty buckets.
            let mut expected = vec![
                (0., 1),
                (5., 1),
                (10., 1),
                (7_500., 1),
                (20_000., 1),
                (120_000., 1),
                (INF, 1),
            ];
            add_to_bucket(&mut expected, if *startup == 0 { 0. } else { 5. }, 1);
            assert_eq!(point.nonzero_buckets(), expected, "{name}");
        }
    }

    #[test]
    fn count_histograms_record_into_count_buckets() {
        let values = [0, 1, 2, 3, 4, 10, 11, 10_000, 10_001];
        for (name, record, startup) in COUNT_HISTOGRAMS {
            let harness = test_metrics();
            for value in values {
                record(&harness.metrics, value);
            }
            let snapshot = harness.collect();
            let point = snapshot.histogram(name, &[]);
            assert_eq!(point.count, values.len() as u64 + 1, "{name}");
            assert_eq!(point.sum, values.iter().sum::<u64>() + startup, "{name}");

            let mut expected = vec![
                (0., 1),
                (1., 1),
                (2., 1),
                (3., 1),
                (5., 1),
                (10., 1),
                (25., 1),
                (10_000., 1),
                (INF, 1),
            ];
            add_to_bucket(&mut expected, *startup as f64, 1);
            assert_eq!(point.nonzero_buckets(), expected, "{name}");
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
}
