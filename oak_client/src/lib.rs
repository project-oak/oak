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
use oak_abi::label::Label;
use prost::Message;
use tonic::{
    metadata::MetadataValue,
    transport::{Certificate, Channel, ClientTlsConfig},
    Request,
};

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

/// Intercepts gRPC requests and adds the same `label` as a gRPC metadata.
// TODO(#1357): Add logic for authenticating Oak clients.
pub struct Interceptor {
    /// Label that is being added to all gRPC requests.
    ///
    /// Is stored as a `Vec<u8>` because encoding a label may fail and `Into<Interceptor>` cannot
    /// return an error.
    label: Vec<u8>,
}

impl Interceptor {
    pub fn create(label: &Label) -> anyhow::Result<Self> {
        let mut encoded_label = Vec::new();
        label
            .encode(&mut encoded_label)
            .context("Error encoding label")?;
        Ok(Self {
            label: encoded_label,
        })
    }
}

impl Into<tonic::Interceptor> for Interceptor {
    fn into(self) -> tonic::Interceptor {
        let interceptor = move |mut request: Request<()>| {
            request.metadata_mut().insert_bin(
                oak_abi::OAK_LABEL_GRPC_METADATA_KEY,
                MetadataValue::from_bytes(self.label.as_ref()),
            );
            Ok(request)
        };
        tonic::Interceptor::new(interceptor)
    }
}
