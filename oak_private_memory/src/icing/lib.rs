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
use bincode::{config, Decode, Encode};
pub use icing_rust_proto::icing::lib::*;

// Rexport the ffi functions from the bridge.
pub mod ffi {
    pub use icing_ffi_bridge::*;
}

const SCHEMA_PB_PATH: &str = "schema_dir/schema.pb";
const OVERLAY_SCHEMA_PB_PATH: &str = "schema_dir/overlay_schema.pb";
const SCHEMA_STORE_HEADER_PATH: &str = "schema_dir/schema_store_header";
const DOCUMENT_LOG_PATH: &str = "document_dir/document_log_v1";

/// Contains all the ground truths files of an icing database,
/// which can be used to rebuild the original database.
/// It allows exporting an icing database as a byte array, so we can
/// store it as a blob.
#[derive(Default, Encode, Decode, PartialEq, Debug)]
pub struct IcingGroundTruthFiles {
    schema_pb: Vec<u8>,
    overlay_schema_pb: Option<Vec<u8>>,
    schema_store_header: Vec<u8>,
    document_log: Vec<u8>,
}

impl IcingGroundTruthFiles {
    pub fn new(base_dir: &str) -> Result<Self> {
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

        let overlay_schema_pb =
            if overlay_schema_pb_path.is_file() {
                Some(fs::read(&overlay_schema_pb_path).with_context(|| {
                    format!("Failed to read {}", overlay_schema_pb_path.display())
                })?)
            } else {
                None
            };

        Ok(Self { schema_pb, overlay_schema_pb, schema_store_header, document_log })
    }

    /// Helper function to create a subdirectory within the new base directory.
    fn create_subdir(base_dir: &Path, subdir_name: &str) -> Result<()> {
        fs::create_dir_all(base_dir.join(subdir_name))
            .with_context(|| format!("Failed to create {} in {}", subdir_name, base_dir.display()))
    }

    /// Helper function to write data to a file within the new base directory.
    fn write_file(base_dir: &Path, relative_path: &str, data: &[u8]) -> Result<()> {
        let target_path = base_dir.join(relative_path);
        fs::write(&target_path, data)
            .with_context(|| format!("Failed to write {}", target_path.display()))
    }

    /// Recreates the ground truth files in the specified new directory path.
    pub fn migrate(&self, new_path: &str) -> Result<()> {
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
        Self::create_subdir(&new_base_dir, "schema_dir")?;
        Self::create_subdir(&new_base_dir, "document_dir")?;

        // Write schema_pb
        Self::write_file(&new_base_dir, SCHEMA_PB_PATH, &self.schema_pb)?;

        // Write overlay_schema_pb if it exists
        if let Some(overlay_data) = &self.overlay_schema_pb {
            Self::write_file(&new_base_dir, OVERLAY_SCHEMA_PB_PATH, overlay_data)?;
        }

        // Write schema_store_header
        Self::write_file(&new_base_dir, SCHEMA_STORE_HEADER_PATH, &self.schema_store_header)?;

        // Write document_log
        Self::write_file(&new_base_dir, DOCUMENT_LOG_PATH, &self.document_log)?;

        Ok(())
    }

    pub fn encode_to_vec(&self) -> Result<Vec<u8>> {
        Ok(bincode::encode_to_vec(&self, config::standard())?)
    }

    pub fn decode_from_slice(buf: &[u8]) -> Result<Self> {
        let (result, _) = bincode::decode_from_slice(buf, config::standard())?;
        Ok(result)
    }
}
