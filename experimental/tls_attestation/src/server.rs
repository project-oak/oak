//
// Copyright 2021 The Project Oak Authors
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

use anyhow::{anyhow, Context};
use futures::future::FutureExt;
use futures_util::stream::Stream;
use http::Uri;
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Client, Request, Response, Server,
};
use log::warn;
use oak_attestation_common::certificate::{AddTeeExtension, CertificateAuthority};
use std::pin::Pin;
use tokio::net::{TcpListener, TcpStream};
use tokio_rustls::{server::TlsStream, TlsAcceptor};

/// Proxies HTTPS requests to an HTTP server specified by `uri`.
async fn proxy(
    request: Request<Body>,
    client: Client<hyper::client::HttpConnector>,
    uri: http::Uri,
) -> Result<Response<Body>, hyper::Error> {
    let (mut parts, body) = request.into_parts();
    parts.uri = uri;

    let proxy_request = Request::from_parts(parts, body);
    client.request(proxy_request).await
}

/// Runs HTTPS proxy server that provides self-signed TLS certificates with TEE attestation
/// credentials inside a custom X.509 extension.
pub async fn run_server(
    address: &str,
    app_uri: Uri,
    tee_certificate: Vec<u8>,
) -> anyhow::Result<()> {
    // Configure TLS settings.
    let identity = Identity::create(tee_certificate).context("Couldn't create TLS identity")?;
    let tls_config = {
        let mut config = rustls::ServerConfig::new(rustls::NoClientAuth::new());
        config
            .set_single_cert(vec![identity.certificate], identity.private_key)
            .map_err(|error| anyhow!("Couldn't set TLS identity: {:?}", error))?;
        // Configure ALPN to accept HTTP/1.1 and HTTP/2.
        config.set_protocols(&[b"http/1.1".to_vec(), b"h2".to_vec()]);
        std::sync::Arc::new(config)
    };
    let tls_acceptor = TlsAcceptor::from(tls_config);

    // Create a TCP listener.
    let address: std::net::SocketAddr = address.parse().context("Couldn't parse address")?;
    let tcp = TcpListener::bind(&address)
        .await
        .map_err(|error| anyhow!("Couldn't bind address: {:?}", error))?;

    // Create a future stream for accepting and serving clients.
    let incoming_tls_stream = async_stream::stream! {
        loop {
            let (socket, _) = tcp.accept().await?;
            match tls_acceptor.accept(socket).await {
                Ok(stream) => yield Ok(stream),
                Err(error) => warn!("TLS client connection error: {:?}", error),
            };
        }
    };

    let client = Client::new();
    let service = make_service_fn(|_conn| {
        let client = client.clone();
        let app_uri = app_uri.clone();
        async {
            Ok::<_, hyper::Error>(service_fn(move |request| {
                proxy(request, client.clone(), app_uri.clone())
            }))
        }
    });
    let server = Server::builder(HyperAcceptor {
        acceptor: Box::pin(incoming_tls_stream),
    })
    .serve(service);

    server
        .with_graceful_shutdown(tokio::signal::ctrl_c().map(|r| r.unwrap()))
        .await
        .map_err(|error| anyhow!("Couldn't run server: {:?}", error))?;
    Ok(())
}

/// Convenience structure for representing TLS identities that include private keys and
/// certificates.
struct Identity {
    private_key: rustls::PrivateKey,
    certificate: rustls::Certificate,
}

impl Identity {
    /// Generates private key and TLS certificate that contains TEE credentials in a custom X.509
    /// extension.
    fn create(tee_certificate: Vec<u8>) -> anyhow::Result<Self> {
        let certificate_authority =
            CertificateAuthority::create(AddTeeExtension::Yes(tee_certificate))
                .context("Couldn't create certificate authority")?;

        let private_key = {
            let key_pair_pem = certificate_authority.get_private_key_pem()?;
            let mut cc_reader = std::io::BufReader::new(&key_pair_pem[..]);
            let private_keys = rustls::internal::pemfile::pkcs8_private_keys(&mut cc_reader)
                .map_err(|error| anyhow!("Couldn't parse private key: {:?}", error))?;
            if private_keys.len() != 1 {
                return Err(anyhow!(
                    "Incorrect number of private keys provided: {}, expected 1",
                    private_keys.len()
                ));
            }
            private_keys[0].clone()
        };

        let certificate = {
            let root_certificate_pem = certificate_authority.get_root_certificate_pem()?;
            let mut cc_reader = std::io::BufReader::new(&root_certificate_pem[..]);
            let certificates = rustls::internal::pemfile::certs(&mut cc_reader)
                .map_err(|error| anyhow!("Couldn't parse certificate: {:?}", error))?;
            if certificates.len() != 1 {
                return Err(anyhow!(
                    "Incorrect number of certificates provided: {}, expected 1",
                    certificates.len()
                ));
            }
            certificates[0].clone()
        };

        Ok(Self {
            private_key,
            certificate,
        })
    }
}

struct HyperAcceptor<'a> {
    acceptor: Pin<Box<dyn Stream<Item = Result<TlsStream<TcpStream>, std::io::Error>> + 'a>>,
}

impl hyper::server::accept::Accept for HyperAcceptor<'_> {
    type Conn = TlsStream<TcpStream>;
    type Error = std::io::Error;

    fn poll_accept(
        mut self: Pin<&mut Self>,
        cx: &mut core::task::Context,
    ) -> core::task::Poll<Option<Result<Self::Conn, Self::Error>>> {
        Pin::new(&mut self.acceptor).poll_next(cx)
    }
}
