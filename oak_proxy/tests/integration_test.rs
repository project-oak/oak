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

use std::{net::TcpListener, process::Command, time::Duration};

use oak_proxy_lib::config::{ClientConfig, ServerConfig};
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::TcpStream,
};

fn find_free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

#[tokio::test]
async fn proxy_test() -> anyhow::Result<()> {
    let client_port = find_free_port();
    let server_proxy_port = find_free_port();
    let backend_port = find_free_port();

    let backend = tokio::spawn(async move {
        let listener =
            tokio::net::TcpListener::bind(format!("127.0.0.1:{}", backend_port)).await.unwrap();
        let (mut socket, _) = listener.accept().await.unwrap();
        let mut buf = Vec::new();
        socket.read_to_end(&mut buf).await.unwrap();
        socket.write_all(&buf).await.unwrap();
        socket.shutdown().await.unwrap();
        assert_eq!(buf, b"Hello, proxy!");
    });

    // Give the backend a moment to start up.
    tokio::time::sleep(Duration::from_secs(1)).await;

    let client_config = ClientConfig {
        listen_address: Some(format!("127.0.0.1:{}", client_port).parse()?),
        server_proxy_url: Some(format!("ws://127.0.0.1:{}", server_proxy_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
    };

    let server_config = ServerConfig {
        listen_address: Some(format!("127.0.0.1:{}", server_proxy_port).parse()?),
        backend_address: Some(format!("127.0.0.1:{}", backend_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        backend_command: None,
    };

    std::fs::write("client.toml", toml::to_string(&client_config)?)?;
    std::fs::write("server.toml", toml::to_string(&server_config)?)?;

    let mut server_proxy = Command::new("oak_proxy/server/server")
        .args([
            "--config",
            "server.toml",
            "--listen-address",
            &server_config.listen_address.unwrap().to_string(),
        ])
        .env("RUST_LOG", "debug")
        .spawn()?;
    let mut client_proxy = Command::new("oak_proxy/client/client")
        .args([
            "--config",
            "client.toml",
            "--listen-address",
            &client_config.listen_address.unwrap().to_string(),
            "--server-proxy-url",
            client_config.server_proxy_url.unwrap().as_ref(),
        ])
        .env("RUST_LOG", "debug")
        .spawn()?;

    // Wait for the processes to start
    tokio::time::sleep(Duration::from_secs(1)).await;

    let mut stream = TcpStream::connect(format!("127.0.0.1:{}", client_port)).await?;
    stream.write_all(b"Hello, proxy!").await?;
    stream.shutdown().await?;
    let mut buf = Vec::new();
    stream.read_to_end(&mut buf).await?;
    assert_eq!(buf, b"Hello, proxy!");

    // Wait for the message to be processed
    tokio::time::sleep(Duration::from_secs(2)).await;

    let _ = backend.await;

    server_proxy.kill()?;
    client_proxy.kill()?;

    Ok(())
}

#[tokio::test]
async fn http_failure_test() -> anyhow::Result<()> {
    let client_port = find_free_port();
    let server_proxy_port = find_free_port(); // We won't start a server here

    let client_config = ClientConfig {
        listen_address: Some(format!("127.0.0.1:{}", client_port).parse()?),
        server_proxy_url: Some(format!("ws://127.0.0.1:{}", server_proxy_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
    };

    let config_path = format!("client_http_fail_{}.toml", client_port);
    std::fs::write(&config_path, toml::to_string(&client_config)?)?;

    let mut client_proxy = Command::new("oak_proxy/client/client")
        .args([
            "--config",
            &config_path,
            "--listen-address",
            &client_config.listen_address.unwrap().to_string(),
            "--server-proxy-url",
            client_config.server_proxy_url.unwrap().as_ref(),
            "--http-error-on-fail",
        ])
        .env("RUST_LOG", "debug")
        .spawn()?;

    // Wait for process to start
    tokio::time::sleep(Duration::from_secs(1)).await;

    // Connect and send simple HTTP request
    let connect_result = async {
         let mut stream = TcpStream::connect(format!("127.0.0.1:{}", client_port)).await?;
         stream.write_all(b"GET / HTTP/1.1\r\n\r\n").await?;
         let mut buf = Vec::new();
         stream.read_to_end(&mut buf).await?;
         Ok::<Vec<u8>, anyhow::Error>(buf)
    }.await;

    // Cleanup first to ensure we don't leave processes running if assert fails
    let _ = client_proxy.kill();
    let _ = std::fs::remove_file(config_path);

    let buf = connect_result?;
    let response = String::from_utf8_lossy(&buf);
    println!("Response: {}", response);
    assert!(response.contains("HTTP/1.1 502 Bad Gateway"));

    Ok(())
}
