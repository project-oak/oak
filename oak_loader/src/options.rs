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

//! Helper functions to parse input arguments and create an instance of
//! `RuntimeConfiguration` to feed into the oak_loader.

use anyhow::{anyhow, Context};
use core::str::FromStr;
use log::debug;
use minisign::{PublicKey, SignatureBox};
use oak_abi::proto::oak::application::{ApplicationConfiguration, ConfigMap};
use oak_runtime::{
    auth::oidc_utils::{parse_client_info_json, ClientInfo},
    config::load_certificate,
    Signature, SignatureTable,
};
use prost::Message;
use std::{
    collections::HashMap,
    fs::{read, read_to_string},
};
use structopt::StructOpt;
use tonic::transport::Identity;

/// Command line options for the Oak loader.
#[derive(StructOpt, Clone, Debug)]
#[structopt(about = "Oak Loader")]
pub struct Opt {
    #[structopt(long, help = "Application configuration file.")]
    application: String,
    #[structopt(long, help = "Private RSA key file used by gRPC server pseudo-Nodes.")]
    grpc_tls_private_key: String,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS certificate file used by gRPC server pseudo-Nodes."
    )]
    grpc_tls_certificate: String,
    // Only support `root-tls-certificate` when `oak_debug` is enabled.
    #[cfg_attr(
        feature = "oak_debug",
        structopt(
            long,
            help = "PEM encoded X.509 TLS root certificate file used to authenticate an external gRPC service."
        )
    )]
    root_tls_certificate: Option<String>,
    #[structopt(
        long,
        help = "Path to a TOML file containing information about Oak modules' signatures."
    )]
    signatures_manifest: Option<String>,
    #[structopt(
        long,
        help = "Path to the downloaded JSON-encoded client identity file for OpenID Connect. \
        OpenID Connect authentication will not be available if this parameter is not specified."
    )]
    oidc_client: Option<String>,
    #[structopt(long, default_value = "9090", help = "Metrics server port number.")]
    metrics_port: u16,
    #[structopt(long, help = "Starts the Runtime without a metrics server.")]
    no_metrics: bool,
    #[structopt(
        long,
        default_value = "1909",
        help = "Introspection server port number."
    )]
    introspect_port: u16,
    #[structopt(long, help = "Starts the Runtime without an introspection server.")]
    no_introspect: bool,
    #[structopt(
        long,
        help = "Configuration files to expose to the Oak Application, each in key=filename format."
    )]
    config_files: Vec<ConfigEntry>,
}

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct SignatureManifest {
    // Maps each module hash to a vector of [`SignatureLocation`].
    signatures: HashMap<String, Vec<SignatureLocation>>,
}

// Paths to public key and signature files.
#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct SignatureLocation {
    public_key: String,
    signature: String,
}

/// A specification of a configuration entry as human readable key and a path to a file whose
/// contents constitutes the actual value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigEntry {
    pub key: String,
    pub filename: String,
}

impl FromStr for ConfigEntry {
    type Err = anyhow::Error;
    fn from_str(v: &str) -> Result<Self, Self::Err> {
        let parts = v.split('=').collect::<Vec<_>>();
        anyhow::ensure!(parts.len() == 2, "could not parse config entry: {}", v);
        Ok(ConfigEntry {
            key: parts[0].to_string(),
            filename: parts[1].to_string(),
        })
    }
}

/// Parse input options and create a `RuntimeConfiguration`.
pub fn create_runtime_config() -> anyhow::Result<oak_runtime::RuntimeConfiguration> {
    let opt = Opt::from_args();
    debug!("parsed opts: {:?}", opt);

    let config_map = parse_config_map(&opt.config_files).context("could not parse config map")?;
    // We only log the keys here, since the values may be secret.
    debug!("parsed config map entries: {:?}", config_map.items.keys());
    // TODO(#689): Pass the `config_map` object to the Runtime instance, and make it available to
    // the running Oak Application.

    // Load application configuration.
    let app_config = create_app_config(&opt).context("could not create app config")?;

    // Create the overall gRPC configuration.
    let grpc_config = create_grpc_config(&opt)?;

    // Create signature table.
    let sign_table = create_sign_table(&opt)?;

    // Create Runtime config.
    let runtime_configuration = oak_runtime::RuntimeConfiguration {
        metrics_port: if cfg!(feature = "oak_debug") && !opt.no_metrics {
            Some(opt.metrics_port)
        } else {
            None
        },
        introspect_port: if cfg!(feature = "oak_debug") && !opt.no_introspect {
            Some(opt.introspect_port)
        } else {
            None
        },
        grpc_config,
        app_config,
        sign_table,
        config_map,
    };

    Ok(runtime_configuration)
}

/// Parse a collection of configuration entries and return the contents of
/// the corresponding files as a [`ConfigMap`].
pub fn parse_config_map(config_entries: &[ConfigEntry]) -> anyhow::Result<ConfigMap> {
    let mut file_map = HashMap::new();
    for config_entry in config_entries {
        anyhow::ensure!(
            !file_map.contains_key(&config_entry.key),
            "duplicate config entry key: {}",
            config_entry.key
        );
        file_map.insert(
            config_entry.key.to_string(),
            read(&config_entry.filename)
                .with_context(|| format!("Couldn't read file {}", &config_entry.filename))?,
        );
    }
    Ok(ConfigMap { items: file_map })
}

/// Create the overall [`oak_runtime::GrpcConfiguration`] from the TLS certificate and private key
/// files.
fn create_grpc_config(opt: &Opt) -> anyhow::Result<oak_runtime::GrpcConfiguration> {
    let grpc_tls_private_key =
        read_to_string(&opt.grpc_tls_private_key).context("could not read gRPC TLS private key")?;
    let grpc_tls_certificate =
        read_to_string(&opt.grpc_tls_certificate).context("could not read gRPC TLS certificate")?;
    let root_tls_certificate = get_root_tls_certificate_or_default(&opt)?;
    let oidc_client_info = get_oidc_client_info(&opt)?;

    let grpc_config = oak_runtime::GrpcConfiguration {
        grpc_server_tls_identity: Some(Identity::from_pem(
            &grpc_tls_certificate,
            &grpc_tls_private_key,
        )),
        grpc_client_root_tls_certificate: Some(
            load_certificate(&root_tls_certificate)
                .map_err(|()| anyhow!("could not parse TLS certificate"))?,
        ),
        oidc_client_info,
    };

    Ok(grpc_config)
}

/// Create a signature table for Oak runtime.
/// Returns an [`oak_runtime::SignatureTable`] that maps each module hash to a vector of
/// [`oak_runtime::Signature`].
/// Returned signatures are not verified yet, they are supposed to be verified by the `oak_runtime`.
fn create_sign_table(opt: &Opt) -> anyhow::Result<SignatureTable> {
    let mut sign_table = SignatureTable::default();

    if let Some(signatures_manifest) = &opt.signatures_manifest {
        let signatures_manifest_file =
            read_to_string(signatures_manifest).context("Couldn't read signature manifest file")?;
        let loaded_signatures_manifest: SignatureManifest = toml::from_str(&signatures_manifest_file)
            .context("Couldn't parse signature manifest file as TOML")?;
        debug!("Parsed signature manifest file: {:?}", signatures_manifest);

        for (module_hash, signature_vec) in loaded_signatures_manifest.signatures.iter() {
            let mut parsed_signatures = vec![];

            for signature_item in signature_vec.iter() {
                debug!("Loading signature for {}", module_hash);
                let public_key = PublicKey::from_file(&signature_item.public_key)
                    .context("Couldn't parse public key file")?;
                debug!("Parsed public key: {}", public_key.to_base64());
                let signature = SignatureBox::from_file(&signature_item.signature)
                    .context("Couldn't parse signature file")?;
                debug!("Parsed signature: {}", signature.to_string());
                parsed_signatures.push(Signature {
                    public_key,
                    signature,
                });
            }

            sign_table
                .values
                .insert(module_hash.to_string(), parsed_signatures);
        }
    }

    Ok(sign_table)
}

/// If `oak_debug` is enabled, read root TLS certificate from the specified file. Otherwise, return
/// the default root TLS certificate from the embedded byte array.
fn get_root_tls_certificate_or_default(opt: &Opt) -> anyhow::Result<String> {
    match &opt.root_tls_certificate {
        Some(certificate_path) => {
            if !cfg!(feature = "oak_debug") {
                // Unreachable: it should not be possible to specify the flag without `oak_debug`.
                anyhow::bail!(
                    "Specifying `root-tls-certificate` requires the `oak_debug` feature."
                );
            };
            read_to_string(certificate_path).context("could not read root TLS certificate")
        }
        None => get_default_root_tls_certs(),
    }
}

/// Parse OpenID Connect client configuration file into a [`ClientInfo`] .
fn get_oidc_client_info(opt: &Opt) -> anyhow::Result<Option<ClientInfo>> {
    match &opt.oidc_client {
        Some(oidc_client) => {
            let oidc_file = read_to_string(oidc_client)
                .context("could not read OpenID Connect client configuration file")?;
            Ok(Some(parse_client_info_json(&oidc_file).map_err(
                |error| anyhow!("Failed to parse json: {:?}", error),
            )?))
        }
        _ => Ok(None),
    }
}

/// Gets the default root TLS certificates from the embedded byte array.
fn get_default_root_tls_certs() -> anyhow::Result<String> {
    let result = std::str::from_utf8(include_bytes!("certs/roots.pem"))
        .context("could not read embedded PEM-encoded root TLS certificates as a UTF8 string")?
        .to_owned();
    Ok(result)
}

/// Parse application configuration into an instance of [`ApplicationConfiguration`]
fn create_app_config(opt: &Opt) -> anyhow::Result<ApplicationConfiguration> {
    let app_config_data =
        read(&opt.application).context("could not read application configuration")?;
    Ok(ApplicationConfiguration::decode(app_config_data.as_ref())
        .context("could not parse application configuration")?)
}
