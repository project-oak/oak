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
    collections::HashSet,
    fs,
    io::Cursor,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result, bail};
// Rexport the ffi functions from the bridge.
pub use icing_ffi_bridge::*;
use icing_rust_proto::icing::lib::scoring_spec_proto::ranking_strategy;
pub use icing_rust_proto::icing::lib::*;
pub use sealed_memory_rust_proto::oak::private_memory::IcingGroundTruthFiles;
use walkdir::WalkDir;

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

        // Read ground truth file contents.
        let schema_pb = fs::read(&schema_pb_path)
            .with_context(|| format!("reading {}", schema_pb_path.display()))?;
        let schema_store_header = fs::read(&schema_store_header_path)
            .with_context(|| format!("reading {}", schema_store_header_path.display()))?;
        let document_log = fs::read(&document_log_path)
            .with_context(|| format!("reading {}", document_log_path.display()))?;

        let overlay_schema_pb = if overlay_schema_pb_path.is_file() {
            fs::read(&overlay_schema_pb_path)
                .with_context(|| format!("reading {}", overlay_schema_pb_path.display()))?
        } else {
            vec![]
        };

        // Tar all non-ground-truth files (index, embedding index, etc.) into
        // directory_snapshot so that import can restore them without rebuilding.
        let directory_snapshot =
            create_directory_snapshot(base_path).context("creating directory snapshot")?;

        Ok(Self {
            schema_pb,
            overlay_schema_pb,
            schema_store_header,
            document_log,
            directory_snapshot,
        })
    }

    /// Recreates the database files in the specified new directory path.
    ///
    /// First restores the four ground truth files (fields 1-4). Then, if
    /// `directory_snapshot` is non-empty, extracts the tar archive on top to
    /// restore index files — eliminating the need for Icing to rebuild indices
    /// on `initialize()`.
    fn migrate(&self, new_path: &str) -> Result<()> {
        let new_base_dir = PathBuf::from(new_path);

        // Ensure the target path is empty by removing it if it exists.
        if new_base_dir.exists() {
            if new_base_dir.is_dir() {
                fs::remove_dir_all(&new_base_dir).with_context(|| {
                    format!("removing existing directory {}", new_base_dir.display())
                })?;
            } else {
                fs::remove_file(&new_base_dir).with_context(|| {
                    format!("removing existing file {}", new_base_dir.display())
                })?;
            }
        }

        // Create base directory and subdirectories for ground truth files.
        create_subdir(&new_base_dir, "schema_dir")?;
        create_subdir(&new_base_dir, "document_dir")?;

        // Write ground truth files.
        write_file(&new_base_dir, SCHEMA_PB_PATH, &self.schema_pb)?;
        if !self.overlay_schema_pb.is_empty() {
            write_file(&new_base_dir, OVERLAY_SCHEMA_PB_PATH, &self.overlay_schema_pb)?;
        }
        write_file(&new_base_dir, SCHEMA_STORE_HEADER_PATH, &self.schema_store_header)?;
        write_file(&new_base_dir, DOCUMENT_LOG_PATH, &self.document_log)?;

        // Extract index files from the directory snapshot if present.
        if !self.directory_snapshot.is_empty() {
            extract_directory_snapshot(&new_base_dir, &self.directory_snapshot)
                .context("extracting directory snapshot")?;
        }

        Ok(())
    }
}

fn create_subdir(base_dir: &Path, subdir_name: &str) -> Result<()> {
    fs::create_dir_all(base_dir.join(subdir_name))
        .with_context(|| format!("Failed to create {} in {}", subdir_name, base_dir.display()))
}

fn write_file(base_dir: &Path, relative_path: &str, data: &[u8]) -> Result<()> {
    let target_path = base_dir.join(relative_path);
    fs::write(&target_path, data).with_context(|| format!("writing {}", target_path.display()))
}

/// Ground truth relative paths that are stored in dedicated proto fields and
/// excluded from the tar archive to avoid duplication.
fn ground_truth_paths() -> HashSet<&'static str> {
    HashSet::from([
        SCHEMA_PB_PATH,
        OVERLAY_SCHEMA_PB_PATH,
        SCHEMA_STORE_HEADER_PATH,
        DOCUMENT_LOG_PATH,
    ])
}

/// Creates a tar archive of all files in `base_dir` except the ground truth
/// files (which are stored in dedicated proto fields).
fn create_directory_snapshot(base_dir: &Path) -> Result<Vec<u8>> {
    let excluded = ground_truth_paths();
    let mut builder = tar::Builder::new(Vec::new());

    for entry in WalkDir::new(base_dir).into_iter() {
        let entry = entry.context("walking directory")?;
        let path = entry.path();
        if !path.is_file() {
            continue;
        }
        let relative = path.strip_prefix(base_dir).context("stripping base dir prefix")?;
        let relative_str = relative.to_str().context("non-utf8 path")?;
        if excluded.contains(relative_str) {
            continue;
        }
        builder
            .append_path_with_name(path, relative)
            .with_context(|| format!("archiving {}", relative_str))?;
    }

    builder.finish().context("finishing tar archive")?;
    builder.into_inner().context("extracting tar bytes")
}

/// Extracts a tar archive into `target_dir`, creating parent directories as
/// needed.
fn extract_directory_snapshot(target_dir: &Path, snapshot: &[u8]) -> Result<()> {
    let cursor = Cursor::new(snapshot);
    let mut archive = tar::Archive::new(cursor);
    archive.unpack(target_dir).context("unpacking directory snapshot")
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
        quantized_values: None,
    }
}
