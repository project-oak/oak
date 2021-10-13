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

use rustls::{
    internal::pemfile::{certs, rsa_private_keys},
    NoClientAuth, ServerConfig,
};
use std::{
    fs::File,
    io::{self, BufReader},
    sync::Arc,
};

/// Represents a PEM formatted certificate.
#[derive(Clone)]
pub struct Certificate {
    pem: Vec<u8>,
}

impl Certificate {
    /// Checks that the input byte vector represents a valid PEM formatted certificate. If so,
    /// creates and returns a certificate from the bytes. Otherwise, returns an error.
    pub fn parse(bytes: Vec<u8>) -> anyhow::Result<Certificate> {
        let mut cursor = std::io::Cursor::new(bytes.clone());

        // `rustls` doesn't specify certificate parsing errors:
        // https://docs.rs/rustls/0.17.0/rustls/internal/pemfile/fn.certs.html
        certs(&mut cursor).map_err(|()| {
            anyhow::Error::msg("The certificate is not a valid PEM formatted certificate")
        })?;

        Ok(Certificate { pem: bytes })
    }
}

impl AsRef<[u8]> for Certificate {
    fn as_ref(&self) -> &[u8] {
        self.pem.as_ref()
    }
}

impl From<Certificate> for tonic::transport::Certificate {
    fn from(certificate: Certificate) -> Self {
        tonic::transport::Certificate::from_pem(certificate)
    }
}

/// Represents TLS identity to use for HTTP server pseudo-nodes.
#[derive(Default, Clone)]
pub struct TlsConfig {
    certs: Vec<rustls::Certificate>,
    keys: Vec<rustls::PrivateKey>,
}

impl TlsConfig {
    pub fn new(cert_path: &str, key_path: &str) -> Option<Self> {
        let certs = match load_certs(cert_path) {
            Ok(certs) => certs,
            Err(_) => return None,
        };

        let keys = match load_keys(key_path) {
            Ok(keys) => keys,
            Err(_) => return None,
        };
        Some(TlsConfig { certs, keys })
    }
}

pub(crate) fn to_server_config(tls_config: TlsConfig) -> Arc<ServerConfig> {
    let mut cfg = ServerConfig::new(NoClientAuth::new());
    // Select a certificate to use.
    let private_key = tls_config.keys[0].clone();
    if let Err(error) = cfg.set_single_cert(tls_config.certs, private_key) {
        log::warn!("{}", error);
    };
    // Configure ALPN to accept HTTP/2, HTTP/1.1 in that order.
    cfg.set_protocols(&[b"h2".to_vec(), b"http/1.1".to_vec()]);
    Arc::new(cfg)
}

fn load_certs(path: &str) -> io::Result<Vec<rustls::Certificate>> {
    certs(&mut BufReader::new(File::open(path)?))
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "invalid cert"))
}

fn load_keys(path: &str) -> io::Result<Vec<rustls::PrivateKey>> {
    rsa_private_keys(&mut BufReader::new(File::open(path)?))
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "invalid key"))
}
