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
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ProtocolEngine,
    ServerSession, Session,
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
    /// The address on which to listen for incoming connections from the client
    /// proxy.
    #[arg(long, default_value = "127.0.0.1:8081")]
    listen_address: SocketAddr,

    /// The address of the backend server to which to forward decrypted traffic.
    #[arg(long, default_value = "127.0.0.1:8080")]
    backend_address: SocketAddr,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let listener = TcpListener::bind(args.listen_address).await?;
    println!("[Server] Listening on {}", args.listen_address);

    loop {
        let (stream, peer_address) = listener.accept().await?;
        println!("[Server] Accepted connection from {}", peer_address);
        let backend_address = args.backend_address;
        tokio::spawn(async move {
            if let Err(err) = handle_connection(stream, backend_address).await {
                eprintln!("[Server] Error handling connection: {:?}", err);
            }
        });
    }
}

async fn handle_connection(
    mut client_stream: TcpStream,
    backend_address: SocketAddr,
) -> anyhow::Result<()> {
    let server_config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    let server_session = Arc::new(Mutex::new(ServerSession::create(server_config)?));

    // Handshake
    {
        let mut session = server_session.lock().await;
        while !session.is_open() {
            let len = client_stream.read_u32().await?;
            let mut buffer = vec![0; len as usize];
            client_stream.read_exact(&mut buffer).await?;
            let request =
                oak_proto_rust::oak::session::v1::SessionRequest::decode(buffer.as_slice())?;
            session.put_incoming_message(request)?;

            if let Some(response) = session.get_outgoing_message()? {
                let response_bytes = response.encode_to_vec();
                client_stream.write_u32(response_bytes.len() as u32).await?;
                client_stream.write_all(&response_bytes).await?;
            }
        }
    }

    println!("[Server] Oak Session established with client proxy.");

    let backend_stream = TcpStream::connect(backend_address).await?;
    println!("[Server] Connected to backend server at {}", backend_address);

    let (mut client_reader, mut client_writer) = client_stream.into_split();
    let (mut backend_reader, mut backend_writer) = backend_stream.into_split();

    let session_clone = server_session.clone();
    let client_to_server = async move {
        loop {
            let len = client_reader.read_u32().await?;
            let mut buffer = vec![0; len as usize];
            client_reader.read_exact(&mut buffer).await?;

            let mut session = session_clone.lock().await;
            session.put_incoming_message(
                oak_proto_rust::oak::session::v1::SessionRequest::decode(buffer.as_slice())?,
            )?;
            if let Some(plaintext) = session.read()? {
                backend_writer.write_all(&plaintext.plaintext).await?;
            }
        }
        #[allow(unreachable_code)]
        Ok::<_, anyhow::Error>(())
    };

    let session_clone = server_session.clone();
    let server_to_client = async move {
        let mut buf = vec![0; 1024];
        loop {
            let n = backend_reader.read(&mut buf).await?;
            if n == 0 {
                break;
            }
            let mut session = session_clone.lock().await;
            session.write(oak_proto_rust::oak::session::v1::PlaintextMessage {
                plaintext: buf[..n].to_vec(),
            })?;
            if let Some(encrypted) = session.get_outgoing_message()? {
                let encrypted_bytes = encrypted.encode_to_vec();
                client_writer.write_u32(encrypted_bytes.len() as u32).await?;
                client_writer.write_all(&encrypted_bytes).await?;
            }
        }
        Ok::<_, anyhow::Error>(())
    };

    tokio::select! {
        res = client_to_server => {
            if let Err(e) = res {
                println!("[Server] Error in client-to-server task: {:?}", e);
            }
        },
        res = server_to_client => {
            if let Err(e) = res {
                println!("[Server] Error in server-to-client task: {:?}", e);
            }
        },
    }

    println!("[Server] Connection closed.");
    Ok(())
}
