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

use std::{
    fs,
    path::{Path, PathBuf},
};

use anyhow::{bail, Context, Result};
// Rexport the ffi functions from the bridge.
pub use icing_ffi_bridge::*;
use icing_rust_proto::icing::lib::scoring_spec_proto::ranking_strategy;
pub use icing_rust_proto::icing::lib::*;
pub use sealed_memory_rust_proto::oak::private_memory::IcingGroundTruthFiles;

use crate::property_proto::VectorProto;

const SCHEMA_PB_PATH: &str = "schema_dir/schema.pb";
const OVERLAY_SCHEMA_PB_PATH: &str = "schema_dir/overlay_schema.pb";
const SCHEMA_STORE_HEADER_PATH: &str = "schema_dir/schema_store_header";
const DOCUMENT_LOG_PATH: &str = "document_dir/document_log_v1";

pub trait IcingGroundTruthFilesHelper {
    fn new(base_dir: &str) -> Result<Self>
    where
        Self: Sized;
    fn migrate(&self, new_path: &str) -> Result<()>;
}

impl IcingGroundTruthFilesHelper for IcingGroundTruthFiles {
    fn new(base_dir: &str) -> Result<Self> {
        let base_dir_path: PathBuf = base_dir.into();
        let base_path = base_dir_path.as_path();
        if !base_path.is_dir() {
            bail!("{} is not a valid directory", base_dir_path.display());
        }
        let schema_pb_path = base_dir_path.join(SCHEMA_PB_PATH);
        let overlay_schema_pb_path = base_dir_path.join(OVERLAY_SCHEMA_PB_PATH);
        let schema_store_header_path = base_dir_path.join(SCHEMA_STORE_HEADER_PATH);
        let document_log_path = base_dir_path.join(DOCUMENT_LOG_PATH);

        if !schema_pb_path.is_file()
            || !schema_store_header_path.is_file()
            || !document_log_path.is_file()
        {
            bail!(
                "Missing some of the required files in {}: {}, {}, {}",
                base_dir_path.display(),
                SCHEMA_PB_PATH,
                SCHEMA_STORE_HEADER_PATH,
                DOCUMENT_LOG_PATH
            );
        }

        // Read file contents
        let schema_pb = fs::read(&schema_pb_path)
            .with_context(|| format!("Failed to read {}", schema_pb_path.display()))?;
        let schema_store_header = fs::read(&schema_store_header_path)
            .with_context(|| format!("Failed to read {}", schema_store_header_path.display()))?;
        let document_log = fs::read(&document_log_path)
            .with_context(|| format!("Failed to read {}", document_log_path.display()))?;

        let overlay_schema_pb = if overlay_schema_pb_path.is_file() {
            fs::read(&overlay_schema_pb_path)
                .with_context(|| format!("Failed to read {}", overlay_schema_pb_path.display()))?
        } else {
            vec![]
        };

        Ok(Self { schema_pb, overlay_schema_pb, schema_store_header, document_log })
    }

    /// Recreates the ground truth files in the specified new directory path.
    fn migrate(&self, new_path: &str) -> Result<()> {
        let new_base_dir = PathBuf::from(new_path);

        // Ensure the target path is empty by removing it if it exists
        if new_base_dir.exists() {
            if new_base_dir.is_dir() {
                fs::remove_dir_all(&new_base_dir).with_context(|| {
                    format!("Failed to remove existing directory {}", new_base_dir.display())
                })?;
            } else {
                fs::remove_file(&new_base_dir).with_context(|| {
                    format!("Failed to remove existing file {}", new_base_dir.display())
                })?;
            }
        }

        // Create base directory and subdirectories
        create_subdir(&new_base_dir, "schema_dir")?;
        create_subdir(&new_base_dir, "document_dir")?;

        // Write schema_pb
        write_file(&new_base_dir, SCHEMA_PB_PATH, &self.schema_pb)?;

        // Write overlay_schema_pb if it exists
        if !self.overlay_schema_pb.is_empty() {
            write_file(&new_base_dir, OVERLAY_SCHEMA_PB_PATH, &self.overlay_schema_pb)?;
        }

        // Write schema_store_header
        write_file(&new_base_dir, SCHEMA_STORE_HEADER_PATH, &self.schema_store_header)?;

        // Write document_log
        write_file(&new_base_dir, DOCUMENT_LOG_PATH, &self.document_log)?;

        Ok(())
    }
}

fn create_subdir(base_dir: &Path, subdir_name: &str) -> Result<()> {
    fs::create_dir_all(base_dir.join(subdir_name))
        .with_context(|| format!("Failed to create {} in {}", subdir_name, base_dir.display()))
}

fn write_file(base_dir: &Path, relative_path: &str, data: &[u8]) -> Result<()> {
    let target_path = base_dir.join(relative_path);
    fs::write(&target_path, data)
        .with_context(|| format!("Failed to write {}", target_path.display()))
}

pub fn get_default_icing_options(base_dir: &str) -> IcingSearchEngineOptions {
    IcingSearchEngineOptions {
        enable_scorable_properties: Some(true),
        build_property_existence_metadata_hits: Some(true),
        base_dir: Some(base_dir.to_string()),
        ..Default::default()
    }
}

pub fn get_default_scoring_spec() -> ScoringSpecProto {
    ScoringSpecProto {
        rank_by: Some(ranking_strategy::Code::DocumentScore.into()),
        ..Default::default()
    }
}

pub fn create_vector_proto(identifier: &str, values: &[f32]) -> VectorProto {
    VectorProto {
        model_signature: Some(identifier.to_string()),
        values: values.to_vec(), // Convert the slice to a Vec<f32>
    }
}
