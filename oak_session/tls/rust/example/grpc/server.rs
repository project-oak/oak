//
// Copyright 2024 The Project Oak Authors
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

use std::sync::Arc;

use clap::Parser;
use oak_session_tls::{OakSessionTlsServerContext, ServerContextConfig};
use oak_session_tls_example_grpc_proto::oak::session::tls::example::{
    TlsSessionRequest, TlsSessionResponse,
    tls_over_grpc_server::{TlsOverGrpc, TlsOverGrpcServer},
};
use tokio::sync::Mutex;
use tokio_stream::wrappers::ReceiverStream;
use tonic::{Request, Response, Status, Streaming, transport::Server};

#[derive(Parser, Debug)]
struct Args {
    #[arg(long, default_value = "8080")]
    port: String,
    #[arg(long, default_value = "oak_session/tls/testing/test_server.key")]
    server_key: String,
    #[arg(long, default_value = "oak_session/tls/testing/test_server.pem")]
    server_cert: String,
}

fn load_cert(path: &str) -> rustls_pki_types::CertificateDer<'static> {
    oak_session_tls::utils::load_cert_der(std::io::BufReader::new(
        std::fs::File::open(path).expect("failed to open cert file"),
    ))
}

fn load_key(path: &str) -> rustls_pki_types::PrivateKeyDer<'static> {
    oak_session_tls::utils::load_key_der(std::io::BufReader::new(
        std::fs::File::open(path).expect("failed to open key file"),
    ))
}

struct MyTlsOverGrpc {
    server_context: Arc<OakSessionTlsServerContext>,
}

impl MyTlsOverGrpc {
    fn new(server_context: OakSessionTlsServerContext) -> Self {
        Self { server_context: Arc::new(server_context) }
    }
}

#[tonic::async_trait]
impl TlsOverGrpc for MyTlsOverGrpc {
    type TlsSessionStream = ReceiverStream<Result<TlsSessionResponse, Status>>;

    async fn tls_session(
        &self,
        request: Request<Streaming<TlsSessionRequest>>,
    ) -> Result<Response<Self::TlsSessionStream>, Status> {
        let (tx, rx) = tokio::sync::mpsc::channel(100);
        let ctx = self.server_context.clone();

        tokio::spawn(async move {
            let stream = Arc::new(Mutex::new(request.into_inner()));
            let tx_clone = tx.clone();
            let stream_clone = stream.clone();

            let res = ctx
                .new_initialized_session(
                    move |frame| {
                        let tx = tx_clone.clone();
                        async move {
                            if tx.send(Ok(TlsSessionResponse { frame })).await.is_err() {
                                return Err(std::io::Error::other("failed to send frame"));
                            }
                            Ok(())
                        }
                    },
                    move || {
                        let stream = stream_clone.clone();
                        async move {
                            match stream.lock().await.message().await {
                                Ok(Some(req)) => Ok(Some(req.frame)),
                                Ok(None) => Ok(None),
                                Err(e) => Err(std::io::Error::other(e)),
                            }
                        }
                    },
                )
                .await;

            let (mut session, initial_data) = match res {
                Ok(s) => s,
                Err(e) => {
                    let _ =
                        tx.send(Err(Status::internal(format!("Handshake failed: {:?}", e)))).await;
                    return;
                }
            };

            if !initial_data.is_empty() {
                let response_data = format!("Hello {}", String::from_utf8_lossy(&initial_data));
                match session.encrypt(response_data.as_bytes()) {
                    Ok(encrypted) => {
                        let _ = tx.send(Ok(TlsSessionResponse { frame: encrypted })).await;
                    }
                    Err(e) => {
                        let _ = tx
                            .send(Err(Status::internal(format!("Encrypt failed: {:?}", e))))
                            .await;
                        return;
                    }
                }
            }

            while let Ok(Some(req)) = stream.lock().await.message().await {
                match session.decrypt(&req.frame) {
                    Ok(decrypted) => {
                        if decrypted.is_empty() {
                            continue;
                        }
                        let response_data =
                            format!("Hello {}", String::from_utf8_lossy(&decrypted));
                        match session.encrypt(response_data.as_bytes()) {
                            Ok(encrypted) => {
                                if tx
                                    .send(Ok(TlsSessionResponse { frame: encrypted }))
                                    .await
                                    .is_err()
                                {
                                    break;
                                }
                            }
                            Err(e) => {
                                let _ = tx
                                    .send(Err(Status::internal(format!("Encrypt failed: {:?}", e))))
                                    .await;
                                break;
                            }
                        }
                    }
                    Err(e) => {
                        let _ = tx
                            .send(Err(Status::internal(format!("Decrypt failed: {:?}", e))))
                            .await;
                        break;
                    }
                }
            }
        });

        Ok(Response::new(ReceiverStream::new(rx)))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let server_key = load_key(&args.server_key);
    let server_cert = load_cert(&args.server_cert);

    let config = ServerContextConfig {
        tls_identity_provider: oak_session_tls::utils::create_static_cert_identity_provider(
            server_key,
            vec![server_cert],
        ),
        client_trust_anchor_provider: None,
        custom_cert_verifier: None,
    };

    let server_context = OakSessionTlsServerContext::create(config).unwrap();

    let addr: std::net::SocketAddr = format!("[::]:{}", args.port).parse()?;

    let svc = TlsOverGrpcServer::new(MyTlsOverGrpc::new(server_context));

    let listener = tokio::net::TcpListener::bind(addr).await?;
    let local_addr = listener.local_addr()?;
    println!("Server listening on port {}", local_addr.port());

    let stream = tokio_stream::wrappers::TcpListenerStream::new(listener);

    Server::builder().add_service(svc).serve_with_incoming(stream).await?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use oak_session_tls::{ClientContextConfig, OakSessionTlsClientContext};
    use oak_session_tls_example_grpc_proto::oak::session::tls::example::tls_over_grpc_client::TlsOverGrpcClient;

    use super::*;

    #[tokio::test]
    async fn test_grpc_session() {
        let server_key = load_key("oak_session/tls/testing/test_server.key");
        let server_cert = load_cert("oak_session/tls/testing/test_server.pem");
        let ca_cert = load_cert("oak_session/tls/testing/test_ca.pem");
        let client_key = load_key("oak_session/tls/testing/test_client.key");
        let client_cert = load_cert("oak_session/tls/testing/test_client.pem");

        let server_config = ServerContextConfig {
            tls_identity_provider: oak_session_tls::utils::create_static_cert_identity_provider(
                server_key,
                vec![server_cert],
            ),
            client_trust_anchor_provider: None,
            custom_cert_verifier: None,
        };
        let server_context = OakSessionTlsServerContext::create(server_config).unwrap();
        let svc = TlsOverGrpcServer::new(MyTlsOverGrpc::new(server_context));

        let listener = tokio::net::TcpListener::bind("[::]:0").await.unwrap();
        let local_addr = listener.local_addr().unwrap();
        let stream = tokio_stream::wrappers::TcpListenerStream::new(listener);

        tokio::spawn(async move {
            Server::builder().add_service(svc).serve_with_incoming(stream).await.unwrap();
        });

        let client_config = ClientContextConfig {
            tls_identity_provider: Some(
                oak_session_tls::utils::create_static_cert_identity_provider(
                    client_key,
                    vec![client_cert],
                ),
            ),
            server_trust_anchor_provider: Some(
                oak_session_tls::utils::create_static_trust_anchor_provider(ca_cert),
            ),
            custom_cert_verifier: None,
            expected_server_name: Some("oak-session-tls".to_string()),
        };
        let client_context = OakSessionTlsClientContext::create(client_config).unwrap();

        let server_address = format!("http://[::1]:{}", local_addr.port());

        // Wait a bit for server to start
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;

        let mut stub = TlsOverGrpcClient::connect(server_address).await.unwrap();

        let (tx, rx) = tokio::sync::mpsc::channel(100);
        let request_stream = tokio_stream::wrappers::ReceiverStream::new(rx);

        let response = stub.tls_session(request_stream).await.unwrap();
        let response_stream = response.into_inner();
        let stream = Arc::new(Mutex::new(response_stream));

        let tx_clone = tx.clone();
        let stream_clone = stream.clone();

        let (mut session, _initial_data) = client_context
            .new_initialized_session(
                move |frame| {
                    let tx = tx_clone.clone();
                    async move {
                        tx.send(TlsSessionRequest { frame })
                            .await
                            .map_err(|_| std::io::Error::other("send failed"))
                    }
                },
                move || {
                    let stream = stream_clone.clone();
                    async move {
                        match stream.lock().await.message().await {
                            Ok(Some(resp)) => Ok(Some(resp.frame)),
                            Ok(None) => Ok(None),
                            Err(e) => Err(std::io::Error::other(e)),
                        }
                    }
                },
            )
            .await
            .unwrap();

        let message = b"world";
        let encrypted = session.encrypt(message).unwrap();
        tx.send(TlsSessionRequest { frame: encrypted }).await.unwrap();

        let mut decrypted = Vec::new();
        while decrypted.is_empty() {
            let resp = stream.lock().await.message().await.unwrap().unwrap();
            decrypted = session.decrypt(&resp.frame).unwrap();
        }

        assert_eq!(String::from_utf8_lossy(&decrypted), "Hello world");
    }
}
