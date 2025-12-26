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

use std::{collections::HashMap, fs, path::Path};

#[derive(thiserror::Error, Debug)]
pub enum ProtoGenError {
    #[error("failed to map OsString filename to String")]
    OsStringError,

    #[error("filename appears to be empty")]
    EmptyFilenameError,

    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}

#[derive(Debug)]
pub struct ProtoLib {
    pub mods: HashMap<String, Mod>,
}

impl ProtoLib {
    /// Generates a [ProtoLib] module tree using the files found in [dir].
    pub fn from_files_in_dir(dir: &Path) -> Result<ProtoLib, ProtoGenError> {
        let files = fs::read_dir(dir)?.collect::<Result<Vec<_>, _>>()?;

        let mut proto_lib = ProtoLib { mods: HashMap::new() };
        for file in files {
            let filename =
                file.file_name().into_string().map_err(|_| ProtoGenError::OsStringError)?;
            let mut filename_parts = filename.split(".");

            // Get a handle on the top-level Rust `mod` implied by this filename.
            let mut current_mod = proto_lib.get_mod(
                filename_parts.next().ok_or(ProtoGenError::EmptyFilenameError)?.to_string(),
            );

            // Recurse down the `mod` tree until we find the `mod` that should include this
            // filename.
            let filename_parts: Vec<_> = filename_parts.collect();
            // Skip the last filename_part because it is (expected to be) "rs".
            for filename_part in filename_parts.clone().into_iter().take(filename_parts.len() - 1) {
                current_mod = current_mod.get_mod(filename_part.to_string());
            }

            // Update the `mod` that should include this filename. There can be only one
            // such included filename per `mod`.
            current_mod.included_filename =
                Some(file.file_name().into_string().map_err(|_| ProtoGenError::OsStringError)?);
        }
        Ok(proto_lib)
    }

    fn get_mod(&mut self, name: String) -> &mut Mod {
        self.mods.entry(name.clone()).or_insert(Mod::new(name))
    }
}

#[derive(Debug)]
pub struct Mod {
    pub name: String,
    pub included_filename: Option<String>,
    pub mods: HashMap<String, Mod>,
}

impl Mod {
    pub(crate) fn new(name: String) -> Self {
        Mod { name, included_filename: None, mods: HashMap::new() }
    }

    pub(crate) fn get_mod(&mut self, name: String) -> &mut Mod {
        self.mods.entry(name.clone()).or_insert(Self::new(name))
    }
}
