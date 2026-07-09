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

use std::{collections::HashSet, io::Read, path::Path, sync::Arc};

use anyhow::Result;
use content_inspector::{ContentType, inspect};
use futures::StreamExt;
use tokei::LanguageType;

/// A file path associated with its identified tags (e.g., language, content
/// type).
#[derive(Debug, Clone)]
pub struct FileWithTags {
    /// The path to the file.
    pub path: String,
    /// A set of tags describing the file's characteristics.
    pub tags: HashSet<String>,
}

/// Identifies tags for multiple files in parallel using tokio tasks.
pub async fn identify_files_parallel(files: &[String]) -> Result<Vec<FileWithTags>> {
    let tokei_config = Arc::new(tokei::Config::default());
    let mut stream = futures::stream::iter(files.iter().cloned())
        .map(|f| {
            let config = tokei_config.clone();
            tokio::spawn(async move {
                let tags = get_tags(Path::new(&f), &config);
                FileWithTags { path: f, tags }
            })
        })
        .buffer_unordered(100);

    let mut results = Vec::new();
    while let Some(res) = stream.next().await {
        results.push(res?);
    }
    Ok(results)
}

/// Analyzes a file at the given path and returns a set of tags describing it.
///
/// The tags are based on content type, language detection, and file naming
/// conventions.
fn get_tags(path: &Path, tokei_config: &tokei::Config) -> HashSet<String> {
    let mut tags = HashSet::new();

    // 1. Content/Text detection
    if let Ok(mut f) = std::fs::File::open(path) {
        let mut buf = [0; 1024];
        if f.read(&mut buf).is_ok_and(|n| inspect(&buf[..n]) != ContentType::BINARY) {
            tags.insert("text".to_string());
        }
    }

    // 2. Language detection via tokei (handles extension, filename, AND shebang)
    if let Some(lang) = LanguageType::from_path(path, tokei_config) {
        tags.insert(format!("{:?}", lang).to_lowercase());
    }

    // 3. Fallback for Bazel files that Tokei might miss or name differently
    if let Some(filename) = path.file_name().and_then(|s| s.to_str()) {
        let is_bazel = matches!(filename, "BUILD" | "WORKSPACE" | "MODULE.bazel")
            || filename.ends_with(".bazel")
            || filename.ends_with(".BUILD")
            || filename.ends_with(".bzl");
        if is_bazel {
            tags.insert("bazel".to_string());
        }
    }

    // 4. Fallback for template files
    if path
        .file_name()
        .and_then(|s| s.to_str())
        .is_some_and(|filename| filename.ends_with(".sh.tpl") || filename.ends_with(".bash.tpl"))
    {
        tags.insert("bash".to_string());
    }
    tags
}
