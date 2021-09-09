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

#[cfg(feature = "oak-attestation")]
use crate::attestation::get_tls_identity_from_proxy;
use anyhow::{anyhow, Context};
use core::str::FromStr;
use log::debug;
use oak_abi::proto::oak::application::{ApplicationConfiguration, ConfigMap};
use oak_runtime::{
    auth::oidc_utils::{parse_client_info_json, ClientInfo},
    permissions::PermissionsConfiguration,
    tls::Certificate,
    SignatureTable,
};
use oak_sign::SignatureBundle;
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
    // `permissions` file is only required with Base servers (with all optional features disabled).
    #[cfg_attr(
        not(feature = "oak-unsafe"),
        structopt(long, help = "Permissions configuration file.")
    )]
    permissions: Option<String>,
    #[structopt(long, help = "Private RSA key file used by gRPC server pseudo-Nodes.")]
    grpc_tls_private_key: Option<String>,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS certificate file used by gRPC server pseudo-Nodes."
    )]
    grpc_tls_certificate: Option<String>,
    // Only support `root-tls-certificate` when `oak-unsafe` is enabled.
    #[cfg_attr(
        feature = "oak-unsafe",
        structopt(
            long,
            help = "PEM encoded X.509 TLS root certificate file used to authenticate an external gRPC service."
        )
    )]
    root_tls_certificate: Option<String>,
    // Only support `proxy-uri` when `oak-attestation` is enabled.
    #[cfg_attr(
        feature = "oak-attestation",
        structopt(long, help = "URI of the Proxy Attestation Service")
    )]
    proxy_uri: Option<String>,
    // Only support `proxy-root-tls-certificate` when `oak-attestation` is enabled.
    #[cfg_attr(
        feature = "oak-attestation",
        structopt(
            long,
            help = "PEM encoded X.509 TLS root certificate file of the Proxy Attestation Service"
        )
    )]
    proxy_root_tls_certificate: Option<String>,
    #[structopt(
        long,
        help = "Path to the downloaded JSON-encoded client identity file for OpenID Connect. \
        OpenID Connect authentication will not be available if this parameter is not specified."
    )]
    oidc_client: Option<String>,
    #[structopt(long, help = "Private RSA key file used by HTTP server pseudo-Nodes.")]
    http_tls_private_key: Option<String>,
    #[structopt(
        long,
        help = "PEM encoded X.509 TLS certificate file used by HTTP server pseudo-Nodes."
    )]
    http_tls_certificate: Option<String>,
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
    #[structopt(long, help = "Filename for KMS credentials.")]
    kms_credentials: Option<String>,
    #[structopt(
        long,
        help = "Configuration files to expose to the Oak Application, each in key=filename format."
    )]
    config_files: Vec<ConfigEntry>,
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
pub async fn create_runtime_config() -> anyhow::Result<oak_runtime::RuntimeConfiguration> {
    let opt = Opt::from_args();
    debug!("parsed opts: {:?}", opt);

    let config_map = parse_config_map(&opt.config_files).context("could not parse config map")?;
    // We only log the keys here, since the values may be secret.
    debug!("parsed config map entries: {:?}", config_map.items.keys());
    // TODO(#689): Pass the `config_map` object to the Runtime instance, and make it available to
    // the running Oak Application.

    // Load application configuration.
    let app_config = create_app_config(&opt).context("could not create app config")?;

    // Load permissions configuration.
    let permissions_config =
        create_permissions_config(&opt).context("could not create app config")?;

    // Create the overall gRPC configuration.
    let secure_server_configuration = create_secure_server_config(&opt).await?;

    // Create signature table.
    let sign_table = create_sign_table(&app_config)?;
    debug!("parsed signatures: {:?}", sign_table);

    // Create Runtime config.
    let runtime_configuration = oak_runtime::RuntimeConfiguration {
        metrics_port: if cfg!(feature = "oak-unsafe") && !opt.no_metrics {
            Some(opt.metrics_port)
        } else {
            None
        },
        introspect_port: if cfg!(feature = "oak-unsafe") && !opt.no_introspect {
            Some(opt.introspect_port)
        } else {
            None
        },
        kms_credentials: opt.kms_credentials.map(std::path::PathBuf::from),
        secure_server_configuration,
        app_config,
        permissions_config,
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

/// Create [`oak_runtime::SecureServerConfiguration`] containing optional TLS configurations for
/// HTTP and gRPC server nodes.
async fn create_secure_server_config(
    opt: &Opt,
) -> anyhow::Result<oak_runtime::SecureServerConfiguration> {
    let grpc_config = create_grpc_config(opt)
        .await
        .context("Couldn't create gRPC config")?;
    let http_config = create_http_config(opt)
        .map_err(|e| log::warn!("{}", e))
        .ok();

    Ok(oak_runtime::SecureServerConfiguration {
        grpc_config: Some(grpc_config),
        http_config,
    })
}

/// Create the overall [`oak_runtime::GrpcConfiguration`] from the TLS certificate and private key
/// files or using the Proxy Attestation Service.
async fn create_grpc_config(opt: &Opt) -> anyhow::Result<oak_runtime::GrpcConfiguration> {
    let tls_identity = get_tls_identity(opt).await?;

    let root_tls_certificate = get_root_tls_certificate_or_default(opt).ok();
    let oidc_client_info = get_oidc_client_info(opt)?;

    let grpc_config = oak_runtime::GrpcConfiguration {
        grpc_server_tls_identity: Some(tls_identity),
        grpc_client_root_tls_certificate: root_tls_certificate,
        oidc_client_info,
    };

    Ok(grpc_config)
}

/// Create a signature table for Oak runtime.
/// Returns an [`SignatureTable`] that maps each module hash to a vector of [`SignatureBundle`].
/// Returned signatures are not verified yet, they are supposed to be verified by the `oak_runtime`.
fn create_sign_table(app_config: &ApplicationConfiguration) -> anyhow::Result<SignatureTable> {
    let mut sign_table = SignatureTable::default();
    for signature in app_config.module_signatures.iter() {
        let bundle: SignatureBundle = signature.to_owned().into();
        bundle.verify().context("Signature verification failed")?;
        let module_hash = hex::encode(&bundle.hash);
        match sign_table.values.get_mut(&module_hash) {
            Some(signatures) => signatures.push(bundle),
            None => {
                sign_table.values.insert(module_hash, vec![bundle]);
            }
        }
    }

    Ok(sign_table)
}

/// Create the overall [`oak_runtime::HttpConfiguration`] from the TLS certificate and private key
/// files.
fn create_http_config(opt: &Opt) -> anyhow::Result<oak_runtime::HttpConfiguration> {
    let http_tls_private_key_path = match &opt.http_tls_private_key {
        Some(path) => path,
        None => {
            return Err(anyhow!(
                "Missing configuration for TLS identity for HTTP server nodes."
            ))
        }
    };
    let http_tls_certificate_path = match &opt.http_tls_certificate {
        Some(path) => path,
        None => {
            return Err(anyhow!(
                "Missing configuration for TLS identity for HTTP server nodes."
            ))
        }
    };

    match oak_runtime::tls::TlsConfig::new(http_tls_certificate_path, http_tls_private_key_path) {
        Some(tls_config) => {
            let root_tls_certificate = get_root_tls_certificate_or_default(opt).ok();
            Ok(oak_runtime::HttpConfiguration {
                tls_config,
                http_client_root_tls_certificate: root_tls_certificate,
            })
        }
        None => Err(anyhow!(
            "Could not create TLS identity for HTTP server nodes."
        )),
    }
}

/// If `oak-unsafe` is enabled, reads root TLS certificate from the specified file into a byte
/// array. Otherwise, loads the default root TLS certificate from the embedded byte array.
/// Parses the byte array into a [`Certificate`], or returns an error if the byte array does not
/// represent a valid PEM formatted certificate.
fn get_root_tls_certificate_or_default(opt: &Opt) -> anyhow::Result<Certificate> {
    let certificate_bytes = match &opt.root_tls_certificate {
        Some(certificate_path) => {
            if !cfg!(feature = "oak-unsafe") {
                // Unreachable: it should not be possible to specify the flag without `oak-unsafe`.
                anyhow::bail!(
                    "Specifying `root-tls-certificate` requires the `oak-unsafe` feature."
                );
            };
            read(certificate_path).context("could not read root TLS certificate")?
        }
        None => get_default_root_tls_certs(),
    };

    Certificate::parse(certificate_bytes)
}

/// Creates [`Identity`] from the TLS certificate and private key files or using the Proxy
/// Attestation Service.
async fn get_tls_identity(opt: &Opt) -> anyhow::Result<Identity> {
    match (&opt.proxy_uri, &opt.proxy_root_tls_certificate) {
        #[cfg(feature = "oak-attestation")]
        (Some(proxy_uri_string), Some(proxy_root_tls_certificate_path)) => {
            let proxy_uri = proxy_uri_string
                .parse()
                .context("Error parsing proxy URI")?;
            let proxy_root_tls_certificate = read_to_string(proxy_root_tls_certificate_path)
                .context("Couldn't read proxy TLS certificate")?;

            get_tls_identity_from_proxy(&proxy_uri, &proxy_root_tls_certificate.as_bytes()).await
        }
        #[cfg(not(feature = "oak-attestation"))]
        (Some(_proxy_uri_string), Some(_proxy_root_tls_certificate_path)) => {
            // Unreachable: it should not be possible to specify the flag without
            // `oak-attestation`.
            Err(anyhow!(
                "Specifying `proxy-uri` or `root-tls-certificate` requires the `oak-attestation` feature."
            ))
        }
        (None, Some(_)) => Err(anyhow!("No proxy URI provided.")),
        (Some(_), None) => Err(anyhow!("No proxy TLS certificate file provided.")),
        (None, None) => {
            let grpc_tls_private_key = match &opt.grpc_tls_private_key {
                Some(path) => read_to_string(path).context("Couldn't read gRPC TLS private key"),
                None => Err(anyhow!("No gRPC TLS private key file provided.")),
            }?;
            let grpc_tls_certificate = match &opt.grpc_tls_certificate {
                Some(path) => read_to_string(path).context("Couldn't read gRPC TLS certificate"),
                None => Err(anyhow!("No gRPC TLS certificate file provided.")),
            }?;

            Ok(Identity::from_pem(
                &grpc_tls_certificate,
                &grpc_tls_private_key,
            ))
        }
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
fn get_default_root_tls_certs() -> Vec<u8> {
    include_bytes!("certs/roots.pem").to_vec()
}

/// Parse application configuration into an instance of [`ApplicationConfiguration`]
fn create_app_config(opt: &Opt) -> anyhow::Result<ApplicationConfiguration> {
    let app_config_data =
        read(&opt.application).context("could not read application configuration")?;
    ApplicationConfiguration::decode(app_config_data.as_ref())
        .context("could not parse application configuration")
}

/// Parse permissions configuration into an instance of [`PermissionsConfiguration`], if
/// `oak-unsafe` is not enabled. Otherwise, use a default [`PermissionsConfiguration`].
fn create_permissions_config(opt: &Opt) -> anyhow::Result<PermissionsConfiguration> {
    match &opt.permissions {
        None => Ok(PermissionsConfiguration::default()),
        Some(permissions) => {
            if cfg!(feature = "oak-unsafe") {
                // Unreachable: it should not be possible to specify the flag with `oak-unsafe`.
                anyhow::bail!("With `oak-unsafe` the `permissions` flag is not available.");
            };
            let permissions_config_data =
                read(permissions).context("could not read permissions configuration")?;
            let permissions: PermissionsConfiguration =
                toml::from_str(std::str::from_utf8(permissions_config_data.as_ref())?)
                    .context("could not parse permissions configuration")?;
            Ok(permissions)
        }
    }
}
