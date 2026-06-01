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

//! Generates the golden icing export snapshot used by the
//! `import_golden_snapshot_preserves_data` test in `icing.rs`.
//!
//! Run via:
//! ```
//! bazel run //database/tools:generate_golden_export -- \
//!     $(pwd)/database/testdata/golden_icing_export.pb
//! ```
//!
//! This writes `database/testdata/golden_icing_export.pb` which must be
//! checked in. Regenerate whenever the schema changes intentionally **and**
//! backward-compatibility has been verified.

use oak_private_memory_database::{IcingMetaDatabase, IcingTempDir, icing::IcingDatabaseConfig};
use prost::Message;
use sealed_memory_rust_proto::oak::private_memory::{Embedding, LlmView, LlmViews, Memory};

fn main() -> anyhow::Result<()> {
    let dir = IcingTempDir::new("golden-export-");
    let mut db = IcingMetaDatabase::new(IcingDatabaseConfig {
        base_dir: dir,
        enable_int8_embedding: false,
    })?;

    // 1. Plain memory with a tag.
    db.add_memory(
        &Memory {
            id: "golden_plain".into(),
            tags: vec!["golden_tag".into()],
            ..Default::default()
        },
        "golden_blob_plain".into(),
    )?;

    // 2. Named memory with timestamps.
    db.add_memory(
        &Memory {
            id: "golden_named".into(),
            name: "my_golden_memory".into(),
            tags: vec!["golden_tag".into()],
            created_timestamp: Some(prost_types::Timestamp { seconds: 1000, nanos: 0 }),
            event_timestamp: Some(prost_types::Timestamp { seconds: 2000, nanos: 0 }),
            ..Default::default()
        },
        "golden_blob_named".into(),
    )?;

    // 3. Memory with an embedding view.
    db.add_memory(
        &Memory {
            id: "golden_view".into(),
            tags: vec!["golden_tag".into(), "view_tag".into()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "golden_view_v1".into(),
                    r#type: "summary".into(),
                    embedding: Some(Embedding {
                        model_signature: "test_model".into(),
                        values: vec![1.0, 0.0, 0.0],
                    }),
                    ..Default::default()
                }],
            }),
            ..Default::default()
        },
        "golden_blob_view".into(),
    )?;

    let exported = db.export()?.encode_to_vec();

    let out_path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "database/testdata/golden_icing_export.pb".to_string());
    std::fs::create_dir_all(
        std::path::Path::new(&out_path).parent().expect("invalid output path"),
    )?;
    std::fs::write(&out_path, &exported)?;
    eprintln!("wrote {} bytes to {}", exported.len(), out_path);
    Ok(())
}
