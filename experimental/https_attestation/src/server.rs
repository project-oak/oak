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
use futures::TryStreamExt;
use futures_util::future::TryFutureExt;
use http::Uri;
use hyper::{service::service_fn, Body, Client, Request, Response};
use log::warn;
use oak_attestation_common::keying_material::{Assertion, KeyingMaterialBundle};
use std::sync::{Arc, Mutex};
use tokio::net::TcpListener;
use tokio_rustls::TlsAcceptor;

#[derive(Clone)]
enum ConnectionStatus {
    Attested,
    NotAttested,
}

/// HTTPS server that terminates TLS connections and works as a proxy for HTTP requests.
///
/// It intercepts HTTP POST requests to `/report` and provides remote attestation to the client in a
/// form of attestation assertions. It also checks attestation assertions generated by the client.
/// All other HTTP requests are forwarded to the `backend_uri`.
///
/// A separate `Proxy` instance is created for each individual TLS session.
#[derive(Clone)]
struct Proxy {
    /// URI of the backend application to proxy HTTP requests to.
    pub backend_uri: http::Uri,
    /// `hyper::Client` used to connect to the backend application.
    pub client: Client<hyper::client::HttpConnector>,
    /// PEM encoded X.509 certificate that signs TEE firmware key.
    pub tee_certificate: Vec<u8>,
    /// Client and server keying material exported from current TLS session.
    pub keying_material_bundle: KeyingMaterialBundle,
    /// Status of the current TLS session.
    /// `Proxy` doesn't proxy HTTP requests to the backend application, while status is
    /// `ConnectionStatus::NotAttested`.
    connection_status: Arc<Mutex<ConnectionStatus>>,
}

impl Proxy {
    fn new(
        backend_uri: http::Uri,
        client: Client<hyper::client::HttpConnector>,
        tee_certificate: Vec<u8>,
        keying_material_bundle: KeyingMaterialBundle,
    ) -> Self {
        Self {
            backend_uri,
            client,
            tee_certificate,
            keying_material_bundle,
            connection_status: Arc::new(Mutex::new(ConnectionStatus::NotAttested)),
        }
    }

    async fn verify_client_assertion(&self, request: Request<Body>) -> anyhow::Result<()> {
        let request_body = hyper::body::to_bytes(request.into_body())
            .await
            .context("Couldn't get request body")?
            .to_vec();
        let serialized_assertion =
            String::from_utf8(request_body).context("Couldn't parse request body")?;
        // Clients currently send empty bodies, so client assertion verification is disabled.
        // TODO(#2048): Implement client assertion generation.
        if !serialized_assertion.is_empty() {
            let assertion = Assertion::from_string(&serialized_assertion)
                .context("Couldn't deserialize client assertion")?;
            assertion
                .verify(&self.keying_material_bundle.client_keying_material)
                .context("Incorrect client assertion")
        } else {
            Ok(())
        }
    }

    fn generate_server_assertion(&self) -> anyhow::Result<String> {
        let assertion = Assertion::generate(
            &self.tee_certificate,
            self.keying_material_bundle.server_keying_material.clone(),
        )
        .context("Couldn't generate server assertion")?;
        assertion
            .to_string()
            .context("Couldn't serialize server assertion")
    }

    fn get_connection_status(&self) -> ConnectionStatus {
        let connection_status = self
            .connection_status
            .lock()
            .expect("Couldn't lock connection status mutex");
        connection_status.clone()
    }

    /// Sets `Proxy::connection_status` to `ConnectionStatus::Attested`.
    fn set_attested_connection_status(&self) {
        let mut connection_status = self
            .connection_status
            .lock()
            .expect("Couldn't lock connection status mutex");
        *connection_status = ConnectionStatus::Attested;
    }
}

/// Proxies HTTPS requests to an HTTP server specified by `backend_uri`.
async fn process_request(
    proxy: Arc<Proxy>,
    request: Request<Body>,
) -> Result<Response<Body>, hyper::Error> {
    match (request.method(), request.uri().path()) {
        (&hyper::Method::POST, "/report") => {
            // Verify client assertion.
            if let Err(error) = proxy.verify_client_assertion(request).await {
                warn!("Incorrect client assertion: {:?}", error);
                return Ok(Response::builder()
                    .status(hyper::StatusCode::UNAUTHORIZED)
                    .body(Body::from("Incorrect client assertion"))
                    .unwrap());
            }
            proxy.set_attested_connection_status();

            // Generate server assertion and send it back to the client.
            match proxy.generate_server_assertion() {
                Ok(assertion) => Ok(Response::new(assertion.into())),
                Err(error) => {
                    warn!("Couldn't generate assertion: {:?}", error);
                    Ok(Response::builder()
                        .status(hyper::StatusCode::INTERNAL_SERVER_ERROR)
                        .body(Body::from("Couldn't generate assertion"))
                        .unwrap())
                }
            }
        }
        _ => match proxy.get_connection_status() {
            ConnectionStatus::Attested => {
                // Proxy HTTP request to `Proxy::backend_uri`.
                let (mut parts, body) = request.into_parts();
                parts.uri = proxy.backend_uri.clone();

                let proxy_request = Request::from_parts(parts, body);
                proxy.client.request(proxy_request).await
            }
            ConnectionStatus::NotAttested => {
                warn!("TLS connection is not attested");
                Ok(Response::builder()
                    .status(hyper::StatusCode::UNAUTHORIZED)
                    .body(Body::from("TLS connection is not attested"))
                    .unwrap())
            }
        },
    }
}

/// Run HTTPS proxy server that implements HTTPS Attestation Service.
pub async fn run_server(
    address: &str,
    private_key: rustls::PrivateKey,
    certificate: rustls::Certificate,
    tee_certificate: Vec<u8>,
    backend_uri: Uri,
) -> anyhow::Result<()> {
    // Configure TLS settings.
    let tls_config = {
        let mut config = rustls::ServerConfig::new(rustls::NoClientAuth::new());
        config
            .set_single_cert(vec![certificate], private_key)
            .map_err(|error| anyhow!("Couldn't set TLS identity: {:?}", error))?;
        // Configure ALPN to accept HTTP/1.1 and HTTP/2.
        config.set_protocols(&[b"http/1.1".to_vec(), b"h2".to_vec()]);
        std::sync::Arc::new(config)
    };
    let tls_acceptor = TlsAcceptor::from(tls_config);

    // Create a TCP listener.
    let address: std::net::SocketAddr = address.parse().context("Couldn't parse address")?;
    let tcp_listener = TcpListener::bind(&address)
        .await
        .map_err(|error| anyhow!("Couldn't bind address: {:?}", error))?;

    // Create a future stream for accepting and serving clients.
    let incoming_tls_streams = async_stream::stream! {
        loop {
            let (socket, _) = tcp_listener.accept().await?;
            let stream = tls_acceptor.accept(socket).map_err(|error| {
                warn!("Client connection error: {:?}", error);
                std::io::Error::new(std::io::ErrorKind::Other, error)
            });
            yield stream.await;
        }
    };
    futures_util::pin_mut!(incoming_tls_streams);

    let client = Client::new();
    // Extract TLS streams from a Future stream in a loop.
    while let Some(tls_stream) = incoming_tls_streams
        .try_next()
        .await
        .context("Couldn't get TLS connection")?
    {
        let keying_material_bundle = {
            let (_, session) = tls_stream.get_ref();
            KeyingMaterialBundle::export(session)?
        };

        let proxy = Arc::new(Proxy::new(
            backend_uri.clone(),
            client.clone(),
            tee_certificate.to_vec(),
            keying_material_bundle,
        ));

        let server = hyper::server::conn::Http::new().serve_connection(
            tls_stream,
            service_fn(move |request| {
                let proxy = proxy.clone();
                async move { process_request(proxy, request).await }
            }),
        );

        // Create a new asynchronous task for processing a newly extracted TLS stream.
        tokio::spawn(async move { server.await });
    }

    Ok(())
}
