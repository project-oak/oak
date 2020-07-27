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
use log::debug;
use oak_abi::proto::oak::application::{
    node_configuration::ConfigType, ApplicationConfiguration, NodeConfiguration,
    WebAssemblyConfiguration,
};
use prost::Message;
use reqwest::Url;
use sha2::{Digest, Sha256};
use std::{collections::HashMap, fs};
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
struct Module {
    path: String,
    url: Option<String>,
    sha256: Option<String>,
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

/// Computes SHA256 sum from `data` and returns it as a HEX encoded string.
fn get_sha256(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hex::encode(hasher.finalize().as_slice().to_vec())
}

/// Download Wasm module from `url` and caches it in `filename`.
async fn download_module_from_url(url: &str, filename: &str) -> anyhow::Result<Vec<u8>> {
    let url: Url = url.parse().context("Couldn't parse URL")?;

    debug!("Downloading module from: {}", url);
    let response = reqwest::get(url.clone())
        .await
        .with_context(|| format!("Couldn't download module from {}", url))?;
    let data = response
        .bytes()
        .await
        .context("Couldn't retrieve module from HTTP response")?
        .to_vec();

    fs::write(filename, &data).with_context(|| format!("Couldn't write file {}", filename))?;
    Ok(data)
}

/// Load Wasm module from file or URL if specified.
/// If file was loaded from URL, it is cached in `module.path`.
async fn load_module(module: &Module) -> anyhow::Result<Vec<u8>> {
    let data = match fs::read(&module.path) {
        Ok(data) => Ok(data),
        Err(error) => match &module.url {
            Some(url) => {
                debug!(
                    "Couldn't load module from cache: {:?}, loading from URL: {}",
                    error, url
                );
                download_module_from_url(&url, &module.path).await
            }
            None => Err(anyhow!("Couldn't read file {}: {:?}", module.path, error)),
        },
    }?;

    match &module.sha256 {
        Some(sha256) => {
            let received_sha256 = get_sha256(&data);
            if received_sha256 == *sha256 {
                Ok(data)
            } else {
                Err(anyhow!(
                    "Incorrect SHA256 sum: expected {}, received {}",
                    sha256,
                    received_sha256
                ))
            }
        }
        None => Ok(data),
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
