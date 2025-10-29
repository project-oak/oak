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

use std::{collections::HashMap, fs, path::PathBuf};

use anyhow::anyhow;
use clap::Parser;
use serde_json::Value;

#[derive(Parser)]
struct Flags {
    #[arg(long, value_delimiter = ',', required = true)]
    files_to_compile: Vec<PathBuf>,

    #[arg(long, value_delimiter = ',', required = true)]
    proto_source_roots: Vec<PathBuf>,

    #[arg(long, required = true)]
    out_filename: PathBuf,

    #[arg(long, required = true)]
    out_dir: PathBuf,

    #[arg(long, required = true)]
    protoc: PathBuf,

    #[arg(long, required = true)]
    extern_paths: String,
}

fn main() -> anyhow::Result<()> {
    let Flags { files_to_compile, proto_source_roots, out_filename, out_dir, protoc, extern_paths } =
        Flags::parse();

    // Generate a file per proto package included in `files_to_compile`.
    micro_rpc_build::compile(
        &files_to_compile,
        &proto_source_roots,
        micro_rpc_build::CompileOptions {
            extern_paths: parse_extern_paths(&extern_paths)?,
            out_dir: Some(out_dir.clone()),
            protoc_executable: Some(protoc),
            ..Default::default()
        },
    );
    let output_files = fs::read_dir(&out_dir)?.collect::<Result<Vec<_>, _>>()?;

    // Generate a single "lib" file in which the per-proto-package files will be
    // included.
    let mut generated_file = File { mods: HashMap::new() };
    for output_file in output_files {
        let filename = output_file
            .file_name()
            .into_string()
            .map_err(|_| anyhow!("failed to map OsString filename to String"))?;
        let mut filename_parts = filename.split(".");

        // Get a handle on the top-level Rust `mod` implied by this filename.
        let mut current_mod = generated_file.get_mod(
            filename_parts.next().ok_or(anyhow!("filename appears to be empty"))?.to_string(),
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
        current_mod.included_file = Some(
            output_file
                .file_name()
                .into_string()
                .map_err(|_| anyhow!("failed to map OsString filename to String"))?,
        );
    }

    // Finally, write out the resulting file (containing `mod` and `include!`
    // statements).
    let out_dir_basename = out_dir
        .file_name()
        .ok_or(anyhow!("out_dir does not have a filename"))?
        .to_str()
        .ok_or(anyhow!("failed to map OsString filename to String"))?;
    fs::write(out_filename, generated_file.as_code(&out_dir_basename.to_string()).as_bytes())?;

    Ok(())
}

fn parse_extern_paths(extern_paths: &str) -> anyhow::Result<Vec<micro_rpc_build::ExternPath>> {
    Ok(match serde_json::from_str(extern_paths)? {
        Value::Object(extern_paths_map) => {
            let mut extern_paths = Vec::new();
            for (key, value) in extern_paths_map {
                extern_paths.push(micro_rpc_build::ExternPath::new(
                    &key,
                    value.as_str().ok_or(anyhow!("unexpected extern_paths type"))?,
                ));
            }
            extern_paths
        }
        _ => anyhow::bail!("unexpected extern_paths type"),
    })
}

#[derive(Debug)]
struct File {
    mods: HashMap<String, Mod>,
}

impl File {
    fn get_mod(&mut self, name: String) -> &mut Mod {
        self.mods.entry(name.clone()).or_insert(Mod::new(name))
    }

    fn as_code(&self, include_prefix: &String) -> String {
        let inner_code = as_code(&mut self.mods.values(), include_prefix);
        format!(
            "
#![no_std]
#![feature(never_type)]
#[allow(unused_imports)]
{inner_code}
"
        )
    }
}

#[derive(Debug)]
struct Mod {
    name: String,
    included_file: Option<String>,
    mods: HashMap<String, Mod>,
}

impl Mod {
    fn new(name: String) -> Self {
        Mod { name, included_file: None, mods: HashMap::new() }
    }

    fn get_mod(&mut self, name: String) -> &mut Mod {
        self.mods.entry(name.clone()).or_insert(Self::new(name))
    }

    fn as_code(&self, include_prefix: &String) -> String {
        let mod_name = &self.name;
        let inner_code = indent(as_code(&mut self.mods.values(), include_prefix));
        match &self.included_file {
            None => {
                format!(
                    "pub mod {mod_name} {{
{inner_code}
}}"
                )
            }
            Some(included_file) => {
                format!(
                    "#[allow(clippy::let_unit_value)]
pub mod {mod_name} {{
    use prost::Message;
    include!(concat!(\"{include_prefix}/{included_file}\"));
{inner_code}
}}"
                )
            }
        }
    }
}

fn as_code(mods: &mut dyn Iterator<Item = &Mod>, include_prefix: &String) -> String {
    mods.map(|inner_mod| inner_mod.as_code(include_prefix)).collect::<Vec<_>>().join("\n")
}

fn indent(str: String) -> String {
    str.split("\n").map(|line| "    ".to_owned() + line).collect::<Vec<_>>().join("\n")
}
