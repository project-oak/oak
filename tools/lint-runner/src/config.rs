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

use std::collections::{HashMap, HashSet};

use regex::Regex;
use serde::Deserialize;

use crate::identify::FileWithTags;

/// Configuration for the lint runner, typically loaded from a TOML file.
#[derive(Debug, Deserialize, Clone)]
#[serde(try_from = "ConfigRaw")]
pub struct Config {
    /// A map of tool identifiers to their respective tool configurations.
    pub tools: HashMap<String, Tool>,

    /// Internal compiled global exclude pattern.
    pub exclude: Option<Regex>,
}

#[derive(Deserialize)]
struct ConfigRaw {
    pub exclude: Option<String>,
    pub tools: HashMap<String, Tool>,
}

impl TryFrom<ConfigRaw> for Config {
    type Error = String;
    fn try_from(mut raw: ConfigRaw) -> Result<Self, Self::Error> {
        let exclude = raw
            .exclude
            .as_ref()
            .map(|s| Regex::new(s).map_err(|e| format!("invalid global exclude regex: {}", e)))
            .transpose()?;

        for (id, tool) in raw.tools.iter_mut() {
            tool.id = id.clone();
        }

        Ok(Config { tools: raw.tools, exclude })
    }
}

impl Config {
    /// Returns the compiled global exclude pattern.
    pub fn get_global_exclude(&self) -> Option<&Regex> {
        self.exclude.as_ref()
    }
}

/// Configuration for an individual linting tool.
#[derive(Debug, Deserialize, Clone)]
#[serde(try_from = "ToolRaw")]
pub struct Tool {
    /// The unique identifier for the tool.
    pub id: String,
    /// An optional human-readable name for the tool.
    pub name: Option<String>,
    /// The command line entry point for the tool.
    pub entry: String,
    /// A list of tags where at least one MUST be present on a file for it to
    /// match this tool.
    pub types: Vec<String>,

    /// Internal compiled file inclusion pattern.
    pub files: Option<Regex>,
    /// Internal compiled tool-specific exclude pattern.
    pub exclude: Option<Regex>,
}

#[derive(Deserialize)]
struct ToolRaw {
    pub name: Option<String>,
    pub entry: String,
    pub files: Option<String>,
    pub exclude: Option<String>,
    #[serde(default)]
    pub types: Vec<String>,
}

impl TryFrom<ToolRaw> for Tool {
    type Error = String;
    fn try_from(raw: ToolRaw) -> Result<Self, Self::Error> {
        let files = raw
            .files
            .as_ref()
            .map(|s| Regex::new(s).map_err(|e| format!("invalid files regex: {}", e)))
            .transpose()?;
        let exclude = raw
            .exclude
            .as_ref()
            .map(|s| Regex::new(s).map_err(|e| format!("invalid exclude regex: {}", e)))
            .transpose()?;

        Ok(Tool {
            id: String::new(), // Injected by Config::try_from
            name: raw.name,
            entry: raw.entry,
            types: raw.types,
            files,
            exclude,
        })
    }
}

pub struct LinterSelection {
    /// Tools that matched at least one file.
    pub active: Vec<Tool>,
    /// Tools that did not match any files.
    pub skipped: Vec<Tool>,
}

impl Tool {
    /// Returns the human-readable name of the tool, falling back to its ID if
    /// no name is provided.
    pub fn display_name(&self) -> &str {
        self.name.as_deref().unwrap_or(&self.id)
    }

    /// Determines if a file matches the tool's inclusion/exclusion criteria and
    /// tags.
    pub fn matches(&self, filename: &str, tags: &HashSet<String>) -> bool {
        if let Some(ref re) = self.exclude {
            if re.is_match(filename) {
                return false;
            }
        }
        if let Some(ref re) = self.files {
            if !re.is_match(filename) {
                return false;
            }
        }
        if !self.types.is_empty() && !self.types.iter().any(|t| tags.contains(t)) {
            return false;
        }
        true
    }
}

/// Selects which tools from the configuration should be active based on the
/// provided files and their tags.
pub fn select_active_tools(config: &Config, file_tags: &[FileWithTags]) -> LinterSelection {
    let mut all_tools: Vec<Tool> = config.tools.values().cloned().collect();

    // Deterministic sort by ID
    all_tools.sort_by(|a, b| a.id.cmp(&b.id));

    let (active, skipped) =
        all_tools.into_iter().partition(|t| file_tags.iter().any(|f| t.matches(&f.path, &f.tags)));

    LinterSelection { active, skipped }
}
