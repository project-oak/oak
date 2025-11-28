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

use std::{fs, path::PathBuf};

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
    let mut compile_config = prost_build::Config::new();
    compile_config.out_dir(out_dir.clone()).protoc_executable(protoc);
    for extern_path in parse_extern_paths(&extern_paths)? {
        compile_config.extern_path(extern_path.proto_path, extern_path.rust_path);
    }
    compile_config.compile_protos(&files_to_compile, &proto_source_roots)?;

    // Finally, write out the resulting file (containing `mod` and `include!`
    // statements).
    let generated_file = proto_gen::ProtoLib::from_files_in_dir(&out_dir)?;
    let out_dir_basename = out_dir
        .file_name()
        .ok_or(anyhow!("out_dir does not have a filename"))?
        .to_str()
        .ok_or(anyhow!("failed to map OsString filename to String"))?;
    fs::write(
        out_filename,
        proto_lib_as_code(&generated_file, &out_dir_basename.to_string()).as_bytes(),
    )?;

    Ok(())
}

#[derive(Default, Clone)]
struct ExternPath {
    proto_path: String,
    rust_path: String,
}

fn parse_extern_paths(extern_paths: &str) -> anyhow::Result<Vec<ExternPath>> {
    Ok(match serde_json::from_str(extern_paths)? {
        Value::Object(extern_paths_map) => {
            let mut extern_paths = Vec::new();
            for (key, value) in extern_paths_map {
                extern_paths.push(ExternPath {
                    proto_path: key,
                    rust_path: value
                        .as_str()
                        .ok_or(anyhow!("unexpected extern_paths type"))?
                        .to_string(),
                });
            }
            extern_paths
        }
        _ => anyhow::bail!("unexpected extern_paths type"),
    })
}

fn proto_lib_as_code(file: &proto_gen::ProtoLib, include_prefix: &String) -> String {
    format!(
        "// Do not lint generated code.
#![allow(clippy::all, clippy::pedantic, clippy::nursery)]
{}",
        mods_as_code(file.mods.values(), include_prefix)
    )
}

fn mod_as_code(module: &proto_gen::Mod, include_prefix: &String) -> String {
    let mod_name = &module.name;
    let inner_code = indent(mods_as_code(module.mods.values(), include_prefix));
    match &module.included_filename {
        None => {
            format!(
                "pub mod {mod_name} {{
{inner_code}
}}"
            )
        }
        Some(included_file) => {
            format!(
                "pub mod {mod_name} {{
    include!(\"{include_prefix}/{included_file}\");
{inner_code}
}}"
            )
        }
    }
}

fn mods_as_code<'a>(
    mods: impl Iterator<Item = &'a proto_gen::Mod>,
    include_prefix: &String,
) -> String {
    mods.map(|inner_mod| mod_as_code(inner_mod, include_prefix)).collect::<Vec<_>>().join("\n")
}

fn indent(str: String) -> String {
    str.split("\n").map(|line| "    ".to_owned() + line).collect::<Vec<_>>().join("\n")
}
