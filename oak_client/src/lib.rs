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

//! Helper library for connecting to Oak from clients.

use anyhow::Context;
use http::uri::Uri;
use tonic::transport::{Certificate, Channel, ClientTlsConfig};

#[cfg(feature = "oak-attestation")]
pub mod attestation;
pub mod interceptors;

/// Creates a TLS channel for connecting to Oak.
pub async fn create_tls_channel(uri: &Uri, root_tls_certificate: &[u8]) -> anyhow::Result<Channel> {
    let tls_config =
        ClientTlsConfig::new().ca_certificate(Certificate::from_pem(root_tls_certificate.to_vec()));
    Channel::builder(uri.clone())
        .tls_config(tls_config)
        .context("Couldn't create TLS configuration")?
        .connect()
        .await
        .context("Couldn't connect to Oak Application")
}
