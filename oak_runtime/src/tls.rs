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

use std::{
    fs::File,
    io::{self, BufReader},
    path::Path,
    sync::Arc,
};
use tokio_rustls::rustls::{
    internal::pemfile::{certs, rsa_private_keys},
    Certificate, NoClientAuth, PrivateKey, ServerConfig,
};

/// Represents TLS identity to use for HTTP server pseudo-nodes.
#[derive(Default, Clone)]
pub struct TlsConfig {
    certs: Vec<Certificate>,
    keys: Vec<PrivateKey>,
}

impl TlsConfig {
    pub fn new(cert_path: &str, key_path: &str) -> Option<Self> {
        let certs = match load_certs(&Path::new(cert_path)) {
            Ok(certs) => certs,
            Err(_) => return None,
        };

        let keys = match load_keys(&Path::new(key_path)) {
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

fn load_certs(path: &Path) -> io::Result<Vec<Certificate>> {
    certs(&mut BufReader::new(File::open(path)?))
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "invalid cert"))
}

fn load_keys(path: &Path) -> io::Result<Vec<PrivateKey>> {
    rsa_private_keys(&mut BufReader::new(File::open(path)?))
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "invalid key"))
}
