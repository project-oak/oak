//
// Copyright 2025 The Project Oak Authors
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

use std::{net::SocketAddr, sync::Arc};

use clap::Parser;
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ClientSession,
    ProtocolEngine, Session,
};
use prost::Message;
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::{TcpListener, TcpStream},
    sync::Mutex,
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The address on which to listen for incoming connections from the
    /// application (e.g., browser).
    #[arg(long, default_value = "127.0.0.1:9090")]
    listen_address: SocketAddr,

    /// The address of the server proxy.
    #[arg(long, default_value = "127.0.0.1:8081")]
    server_proxy_address: SocketAddr,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let listener = TcpListener::bind(args.listen_address).await?;
    println!("[Client] Listening on {}", args.listen_address);

    loop {
        let (stream, peer_address) = listener.accept().await?;
        println!("[Client] Accepted connection from {}", peer_address);
        let server_proxy_address = args.server_proxy_address;
        tokio::spawn(async move {
            if let Err(err) = handle_connection(stream, server_proxy_address).await {
                eprintln!("[Client] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn handle_connection(
    app_stream: TcpStream,
    server_proxy_address: SocketAddr,
) -> anyhow::Result<()> {
    let mut server_proxy_stream = TcpStream::connect(server_proxy_address).await?;
    println!("[Client] Connected to server proxy at {}", server_proxy_address);

    let client_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let client_session = Arc::new(Mutex::new(ClientSession::create(client_config)?));

    // Handshake
    {
        let mut session = client_session.lock().await;
        while !session.is_open() {
            if let Some(request) = session.get_outgoing_message()? {
                let request_bytes = request.encode_to_vec();
                server_proxy_stream.write_u32(request_bytes.len() as u32).await?;
                server_proxy_stream.write_all(&request_bytes).await?;
            }

            if !session.is_open() {
                let len = server_proxy_stream.read_u32().await?;
                let mut buffer = vec![0; len as usize];
                server_proxy_stream.read_exact(&mut buffer).await?;
                let response =
                    oak_proto_rust::oak::session::v1::SessionResponse::decode(buffer.as_slice())?;
                session.put_incoming_message(response)?;
            }
        }
    }

    println!("[Client] Oak Session established with server proxy.");

    let (mut app_reader, mut app_writer) = app_stream.into_split();
    let (mut server_proxy_reader, mut server_proxy_writer) = server_proxy_stream.into_split();

    let session_clone = client_session.clone();
    let client_to_server = async move {
        let mut buf = vec![0; 1024];
        loop {
            let n = app_reader.read(&mut buf).await?;
            if n == 0 {
                break;
            }
            let mut session = session_clone.lock().await;
            session.write(oak_proto_rust::oak::session::v1::PlaintextMessage {
                plaintext: buf[..n].to_vec(),
            })?;
            if let Some(encrypted) = session.get_outgoing_message()? {
                let encrypted_bytes = encrypted.encode_to_vec();
                server_proxy_writer.write_u32(encrypted_bytes.len() as u32).await?;
                server_proxy_writer.write_all(&encrypted_bytes).await?;
            }
        }
        Ok::<_, anyhow::Error>(())
    };

    let session_clone = client_session.clone();
    let server_to_client = async move {
        loop {
            let len = server_proxy_reader.read_u32().await?;
            let mut buffer = vec![0; len as usize];
            server_proxy_reader.read_exact(&mut buffer).await?;

            let mut session = session_clone.lock().await;
            session.put_incoming_message(
                oak_proto_rust::oak::session::v1::SessionResponse::decode(buffer.as_slice())?,
            )?;
            if let Some(plaintext) = session.read()? {
                app_writer.write_all(&plaintext.plaintext).await?;
            }
        }
        #[allow(unreachable_code)]
        Ok::<_, anyhow::Error>(())
    };

    tokio::select! {
        res = client_to_server => {
            if let Err(e) = res {
                println!("[Client] Error in client-to-server task: {:?}", e);
            }
        },
        res = server_to_client => {
            if let Err(e) = res {
                println!("[Client] Error in server-to-client task: {:?}", e);
            }
        },
    }

    println!("[Client] Connection closed.");
    Ok(())
}
