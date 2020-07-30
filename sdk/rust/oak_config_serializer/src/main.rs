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

//! An utility for serializing an Oak application configuration.
//!
//! Invoke with:
//!
//! ```shell
//! cargo run --manifest-path=oak/server/rust/oak_config_serializer/Cargo.toml -- \
//!     --input-file=<CONFIGURATION_FILE> \
//!     --output-file=<OUTPUT_FILE>
//! ```

use anyhow::{anyhow, Context};
use log::{debug, info};
use oak_abi::proto::oak::application::{
    node_configuration::ConfigType, ApplicationConfiguration, NodeConfiguration,
    WebAssemblyConfiguration,
};
use prost::Message;
use reqwest::Url;
use sha2::{Digest, Sha256};
use std::{collections::HashMap, fs, path};
use structopt::StructOpt;

/// Command line options for the Oak Application Configuration Serializer.
#[derive(StructOpt, Clone, Debug)]
#[structopt(about = "Oak Application Configuration Serializer")]
struct Opt {
    #[structopt(long, help = "Input application configuration file in TOML format")]
    input_file: String,
    #[structopt(long, help = "Output file")]
    output_file: String,
}

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
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

/// Directory used to save downloaded Wasm modules.
/// Created in the `std::env::current_dir()`.
const CACHE_DIRECTORY: &str = ".oak";

/// Get path for caching a downloaded file in the [`CACHE_DIRECTORY`].
/// Cache file is named after `sha256_sum`.
fn get_module_cache_path(sha256_sum: &str) -> path::PathBuf {
    let mut cache_path = std::env::current_dir().unwrap();
    cache_path.push(CACHE_DIRECTORY);
    cache_path.push(&sha256_sum);
    cache_path
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
async fn load_module(module: &Module) -> anyhow::Result<Vec<u8>> {
    match &module {
        Module::Path(path) => {
            fs::read(&path).with_context(|| format!("Couldn't read file {}", path))
        }
        Module::External(external) => {
            // Try to load module from cache, if failed, download it from URL.
            let cache_path = get_module_cache_path(&external.sha256);
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
    filename: &str,
) -> anyhow::Result<()> {
    let mut bytes = Vec::new();
    app_config
        .encode(&mut bytes)
        .context("Couldn't encode application configuration")?;
    fs::write(filename, &bytes).with_context(|| format!("Couldn't write file {}", filename))?;
    Ok(())
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();

    let opt = Opt::from_args();
    debug!("Parsed opts: {:?}", opt);

    let input_file = fs::read_to_string(opt.input_file).context("Couldn't read input file")?;
    let config: Config = toml::from_str(&input_file).context("Couldn't parse TOML config file")?;
    debug!("Parsed config file: {:?}", config);

    // Load Wasm modules.
    let mut modules = HashMap::new();
    for (name, module) in config.modules.iter() {
        let loaded_module = load_module(&module).await.context("Couldn't load module")?;
        modules.insert(name.to_string(), loaded_module);
    }

    // Create application configuration.
    let app_config = ApplicationConfiguration {
        wasm_modules: modules,
        initial_node_configuration: Some(NodeConfiguration {
            name: config.name,
            config_type: Some(ConfigType::WasmConfig(WebAssemblyConfiguration {
                wasm_module_name: config.initial_node_configuration.wasm_module_name,
                wasm_entrypoint_name: config.initial_node_configuration.wasm_entrypoint_name,
            })),
        }),
    };

    // Serialize application configuration.
    write_config_to_file(&app_config, &opt.output_file)
        .context("Couldn't write serialized config")?;

    Ok(())
}
