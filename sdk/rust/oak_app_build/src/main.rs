//
// Copyright 2020 The Project Oak Authors
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

//! An utility for building an Oak application from a manifest file.
//!
//! Invoke with:
//!
//! ```shell
//! cargo run --manifest-path=sdk/rust/oak_app_build/Cargo.toml -- \
//!     --manifest-path=<OAK_APP_MANIFEST_FILE>
//! ```
//!
//! The compiled Oak application will then be stored under a `bin` subdirectory from the manifest
//! file location, named after the name field from the app manifest, and with an `.oak` extension.

use anyhow::{anyhow, Context};
use log::{debug, info};
use oak_abi::proto::oak::application::{
    node_configuration::ConfigType, ApplicationConfiguration, NodeConfiguration,
    WebAssemblyConfiguration,
};
use prost::Message;
use reqwest::Url;
use sha2::{Digest, Sha256};
use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
};
use structopt::StructOpt;

/// Command line options for the Oak Application builder.
#[derive(StructOpt, Clone, Debug)]
#[structopt(about = "Oak Application Builder")]
struct Opt {
    #[structopt(long, help = "Input application manifest file in TOML format")]
    manifest_path: String,
}

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    name: String,
    modules: HashMap<String, Module>,
    #[serde(default)]
    initial_node_configuration: InitialNodeConfig,
}

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
enum Module {
    #[serde(rename = "path")]
    Path(String),
    #[serde(rename = "external")]
    External(External),
}

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct External {
    url: String,
    sha256: String,
}

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct InitialNodeConfig {
    wasm_module_name: String,
    wasm_entrypoint_name: String,
}

impl Default for InitialNodeConfig {
    fn default() -> Self {
        Self {
            wasm_module_name: "app".to_string(),
            wasm_entrypoint_name: "oak_main".to_string(),
        }
    }
}

/// Directory used to save build artifacts.
///
/// Relative to the directory containing the app manifest file.
const OUTPUT_DIRECTORY: &str = "bin";

/// Directory used to save downloaded Wasm modules.
///
/// Relative to the directory containing the app manifest file.
const CACHE_DIRECTORY: &str = "bin/cache";

/// Get path for caching a downloaded file in [`CACHE_DIRECTORY`].
/// Cache file is named after `sha256_sum`.
fn get_module_cache_path(manifest_dir: &Path, module_sha256_sum: &str) -> PathBuf {
    manifest_dir.join(CACHE_DIRECTORY).join(&module_sha256_sum)
}

/// Get path for the output application file in [`OUTPUT_DIRECTORY`].
fn get_output_path(manifest_dir: &Path, app_name: &str) -> PathBuf {
    manifest_dir
        .join(OUTPUT_DIRECTORY)
        .join(format!("{}.oak", app_name))
}

/// Computes SHA256 sum from `data` and returns it as a HEX encoded string.
fn get_sha256(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hex::encode(hasher.finalize().as_slice().to_vec())
}

/// Download file from `url`.
async fn download_file_from_url(url: &str) -> anyhow::Result<Vec<u8>> {
    let url: Url = url
        .parse()
        .with_context(|| format!("Couldn't parse URL {}", url))?;

    let response = reqwest::get(url.clone())
        .await
        .with_context(|| format!("Couldn't download file from {}", url))?;
    let data = response
        .bytes()
        .await
        .context("Couldn't retrieve file from HTTP response")?
        .to_vec();
    Ok(data)
}

/// Load Wasm module from file or URL if specified.
/// If the file was downloaded from URL, it is cached in [`CACHE_DIRECTORY`].
async fn load_module(manifest_dir: &Path, module: &Module) -> anyhow::Result<Vec<u8>> {
    match &module {
        Module::Path(path) => {
            fs::read(&path).with_context(|| format!("Couldn't read file {}", path))
        }
        Module::External(external) => {
            // Try to load module from cache, if failed, download it from URL.
            let cache_path = get_module_cache_path(&manifest_dir, &external.sha256);
            let data = match fs::read(&cache_path) {
                Ok(data) => {
                    info!("Loaded module from cache {:?}", cache_path.as_path());
                    data
                }
                Err(_) => {
                    info!(
                        "Couldn't load module from cache {:?}, downloading from URL {}",
                        cache_path.as_path(),
                        external.url,
                    );
                    let data = download_file_from_url(&external.url).await?;

                    // Save the downloaded Wasm module into the cache directory.
                    std::fs::create_dir_all(cache_path.parent().unwrap())
                        .context("Couldn't create cache directory")?;
                    fs::write(&cache_path, &data).with_context(|| {
                        format!("Couldn't write file {:?}", cache_path.as_path())
                    })?;
                    data
                }
            };

            // Check SHA256 sum of the Wasm module.
            let sha256_sum = get_sha256(&data);
            if sha256_sum == external.sha256 {
                Ok(data)
            } else {
                Err(anyhow!(
                    "Incorrect SHA256 sum: expected {}, received {}",
                    external.sha256,
                    sha256_sum
                ))
            }
        }
    }
}

/// Serializes an application configuration from `app_config` and writes it into `filename`.
pub fn write_config_to_file(
    app_config: &ApplicationConfiguration,
    filename: &Path,
) -> anyhow::Result<()> {
    let mut bytes = Vec::new();
    app_config
        .encode(&mut bytes)
        .context("Couldn't encode application configuration")?;
    fs::write(filename, &bytes)
        .with_context(|| format!("Couldn't write file {}", filename.display()))?;
    Ok(())
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();

    let opt = Opt::from_args();
    debug!("Parsed opts: {:?}", opt);

    let manifest_path = Path::new(&opt.manifest_path);
    let manifest_dir = manifest_path
        .parent()
        .context("Couldn't find manifest directory")?;

    let manifest_file = fs::read_to_string(manifest_path).context("Couldn't read manifest file")?;
    let manifest: Manifest =
        toml::from_str(&manifest_file).context("Couldn't parse manifest file as TOML")?;
    debug!("Parsed manifest file: {:?}", manifest);

    // Load Wasm modules.
    let mut modules = HashMap::new();
    for (name, module) in manifest.modules.iter() {
        let loaded_module = load_module(&manifest_dir, &module)
            .await
            .context("Couldn't load module")?;
        modules.insert(name.to_string(), loaded_module);
    }

    // Create application configuration.
    let app_config = ApplicationConfiguration {
        wasm_modules: modules,
        initial_node_configuration: Some(NodeConfiguration {
            name: manifest.name.clone(),
            config_type: Some(ConfigType::WasmConfig(WebAssemblyConfiguration {
                wasm_module_name: manifest.initial_node_configuration.wasm_module_name,
                wasm_entrypoint_name: manifest.initial_node_configuration.wasm_entrypoint_name,
            })),
        }),
    };

    let output_file = get_output_path(&manifest_dir, &manifest.name);

    // Serialize application.
    write_config_to_file(&app_config, &output_file).context("Couldn't write serialized config")?;

    Ok(())
}
