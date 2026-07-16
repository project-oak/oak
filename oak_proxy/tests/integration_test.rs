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

use anyhow::Context;
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
        mode: oak_proxy_lib::config::ProxyMode::default(),
        listen_address: Some(format!("127.0.0.1:{}", client_port).parse()?),
        server_proxy_url: Some(format!("ws://127.0.0.1:{}", server_proxy_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        attestation_output_file: None,
        experimental_tls_session: false,
        tls_ca: None,
    };

    let server_config = ServerConfig {
        mode: oak_proxy_lib::config::ProxyMode::default(),
        listen_address: Some(format!("127.0.0.1:{}", server_proxy_port).parse()?),
        backend_address: Some(format!("127.0.0.1:{}", backend_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        backend_command: None,
        experimental_tls_session: false,
        tls_cert: None,
        tls_key: None,
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
async fn tls_proxy_test() -> anyhow::Result<()> {
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
        assert_eq!(buf, b"Hello, TLS proxy!");
    });

    // Give the backend a moment to start up.
    tokio::time::sleep(Duration::from_secs(1)).await;

    let client_config = ClientConfig {
        mode: oak_proxy_lib::config::ProxyMode::default(),
        listen_address: Some(format!("127.0.0.1:{}", client_port).parse()?),
        server_proxy_url: Some(format!("ws://127.0.0.1:{}", server_proxy_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        attestation_output_file: None,
        experimental_tls_session: true,
        tls_ca: Some("oak_session/tls/testing/test_ca.pem".to_string()),
    };

    let server_config = ServerConfig {
        mode: oak_proxy_lib::config::ProxyMode::default(),
        listen_address: Some(format!("127.0.0.1:{}", server_proxy_port).parse()?),
        backend_address: Some(format!("127.0.0.1:{}", backend_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        backend_command: None,
        experimental_tls_session: true,
        tls_cert: Some("oak_session/tls/testing/test_server.pem".to_string()),
        tls_key: Some("oak_session/tls/testing/test_server.key".to_string()),
    };

    std::fs::write("client_tls.toml", toml::to_string(&client_config)?)?;
    std::fs::write("server_tls.toml", toml::to_string(&server_config)?)?;

    let mut server_proxy = Command::new("oak_proxy/server/server")
        .args([
            "--config",
            "server_tls.toml",
            "--listen-address",
            &server_config.listen_address.unwrap().to_string(),
        ])
        .env("RUST_LOG", "debug")
        .spawn()?;
    let mut client_proxy = Command::new("oak_proxy/client/client")
        .args([
            "--config",
            "client_tls.toml",
            "--listen-address",
            &client_config.listen_address.unwrap().to_string(),
            "--server-proxy-url",
            client_config.server_proxy_url.unwrap().as_ref(),
        ])
        .env("RUST_LOG", "debug")
        .spawn()?;

    // Wait for the processes to start
    tokio::time::sleep(Duration::from_secs(2)).await;

    let mut stream = TcpStream::connect(format!("127.0.0.1:{}", client_port)).await?;
    stream.write_all(b"Hello, TLS proxy!").await?;
    stream.shutdown().await?;
    let mut buf = Vec::new();
    stream.read_to_end(&mut buf).await?;
    assert_eq!(buf, b"Hello, TLS proxy!");

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
    let server_proxy_port = find_free_port(); // No server listening on this port

    let client_config = ClientConfig {
        mode: oak_proxy_lib::config::ProxyMode::Http,
        listen_address: Some(format!("127.0.0.1:{}", client_port).parse()?),
        server_proxy_url: Some(format!("ws://127.0.0.1:{}", server_proxy_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        attestation_output_file: None,
        experimental_tls_session: false,
        tls_ca: None,
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
            "--http",
        ])
        .env("RUST_LOG", "debug")
        .spawn()?;

    // Wait for process to start
    tokio::time::sleep(Duration::from_secs(1)).await;

    let connect_result = async {
        let mut stream = TcpStream::connect(format!("127.0.0.1:{}", client_port)).await?;
        stream.write_all(b"GET / HTTP/1.1\r\n\r\n").await?;
        let mut buf = Vec::new();
        stream.read_to_end(&mut buf).await?;
        Ok::<Vec<u8>, anyhow::Error>(buf)
    }
    .await;

    let _ = client_proxy.kill();
    let _ = std::fs::remove_file(config_path);

    let buf = connect_result?;
    let response = String::from_utf8_lossy(&buf);
    println!("Response: {}", response);
    assert!(response.contains("HTTP/1.1 502 Bad Gateway"));

    // Extract JSON body right after the HTTP header double-newline boundary
    if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
        let json_slice = &buf[pos + 4..];
        let parsed_json: serde_json::Value =
            serde_json::from_slice(json_slice).context("failed to parse HTTP 502 JSON body")?;
        assert_eq!(parsed_json["error_code"], "upstream_connection_failed");
        assert!(
            parsed_json["details"]["failure_reason"]
                .as_str()
                .unwrap()
                .contains("Connection refused")
                || parsed_json["details"]["failure_reason"].as_str().unwrap().contains("connect")
        );
        assert!(parsed_json["timestamp"].is_string());
    } else {
        anyhow::bail!("HTTP 502 response did not contain double-newline boundary");
    }

    Ok(())
}

#[tokio::test]
async fn http_attestation_splicing_test() -> anyhow::Result<()> {
    let backend_port = find_free_port();
    let server_proxy_port = find_free_port();
    let client_port = find_free_port();

    let backend = tokio::net::TcpListener::bind(format!("127.0.0.1:{}", backend_port)).await?;
    let _backend_task = tokio::spawn(async move {
        while let Ok((mut socket, _)) = backend.accept().await {
            tokio::spawn(async move {
                let mut buf = vec![0; 1024];
                if let Ok(n) = socket.read(&mut buf).await {
                    let req = String::from_utf8_lossy(&buf[..n]);
                    // Verify the backend does not receive X-Oak-Attestation header when unattested
                    // (C1)
                    assert!(!req.contains("X-Oak-Attestation:"));
                    let _ = socket
                        .write_all(
                            b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 2\r\n\r\nOK",
                        )
                        .await;
                }
            });
        }
    });

    tokio::time::sleep(Duration::from_secs(1)).await;

    let client_config = ClientConfig {
        mode: oak_proxy_lib::config::ProxyMode::Http,
        listen_address: Some(format!("127.0.0.1:{}", client_port).parse()?),
        server_proxy_url: Some(format!("ws://127.0.0.1:{}", server_proxy_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        attestation_output_file: None,
        experimental_tls_session: false,
        tls_ca: None,
    };

    let server_config = ServerConfig {
        mode: oak_proxy_lib::config::ProxyMode::Http,
        listen_address: Some(format!("127.0.0.1:{}", server_proxy_port).parse()?),
        backend_address: Some(format!("127.0.0.1:{}", backend_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        backend_command: None,
        experimental_tls_session: false,
        tls_cert: None,
        tls_key: None,
    };

    let client_cfg_path = format!("client_http_splicing_{}.toml", client_port);
    let server_cfg_path = format!("server_http_splicing_{}.toml", server_proxy_port);
    std::fs::write(&client_cfg_path, toml::to_string(&client_config)?)?;
    std::fs::write(&server_cfg_path, toml::to_string(&server_config)?)?;

    let mut server_proxy = Command::new("oak_proxy/server/server")
        .args(["--config", &server_cfg_path, "--http"])
        .env("RUST_LOG", "debug")
        .spawn()?;

    tokio::time::sleep(Duration::from_secs(1)).await;

    let mut client_proxy = Command::new("oak_proxy/client/client")
        .args(["--config", &client_cfg_path, "--http"])
        .env("RUST_LOG", "debug")
        .spawn()?;

    tokio::time::sleep(Duration::from_secs(1)).await;

    let connect_result = async {
        let mut stream = TcpStream::connect(format!("127.0.0.1:{}", client_port)).await?;
        stream.write_all(b"GET / HTTP/1.1\r\nHost: localhost\r\n\r\n").await?;
        let mut buf = Vec::new();
        stream.read_to_end(&mut buf).await?;
        Ok::<Vec<u8>, anyhow::Error>(buf)
    }
    .await;

    let _ = client_proxy.kill();
    let _ = server_proxy.kill();
    let _ = std::fs::remove_file(client_cfg_path);
    let _ = std::fs::remove_file(server_cfg_path);

    let buf = connect_result?;
    let response = String::from_utf8_lossy(&buf);
    println!("Splicing Response: {}", response);
    assert!(response.contains("HTTP/1.1 200 OK"));
    // Verify the client proxy does not splice X-Oak-Attestation when unattested
    // (C1)
    assert!(!response.contains("X-Oak-Attestation:"));

    Ok(())
}

#[tokio::test]
async fn http_keep_alive_splicing_test() -> anyhow::Result<()> {
    let backend_port = find_free_port();
    let server_proxy_port = find_free_port();
    let client_port = find_free_port();

    let backend = tokio::net::TcpListener::bind(format!("127.0.0.1:{}", backend_port)).await?;
    let _backend_task = tokio::spawn(async move {
        while let Ok((mut socket, _)) = backend.accept().await {
            tokio::spawn(async move {
                let mut buf = vec![0; 1024];
                // Loop handling multiple sequential requests over keep-alive
                while let Ok(n) = socket.read(&mut buf).await {
                    if n == 0 {
                        break;
                    }
                    let req = String::from_utf8_lossy(&buf[..n]);
                    assert!(!req.contains("X-Oak-Attestation:"));
                    let _ = socket
                        .write_all(
                            b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 2\r\n\r\nOK",
                        )
                        .await;
                }
            });
        }
    });

    tokio::time::sleep(Duration::from_secs(1)).await;

    let client_config = ClientConfig {
        mode: oak_proxy_lib::config::ProxyMode::Http,
        listen_address: Some(format!("127.0.0.1:{}", client_port).parse()?),
        server_proxy_url: Some(format!("ws://127.0.0.1:{}", server_proxy_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        attestation_output_file: None,
        experimental_tls_session: false,
        tls_ca: None,
    };

    let server_config = ServerConfig {
        mode: oak_proxy_lib::config::ProxyMode::Http,
        listen_address: Some(format!("127.0.0.1:{}", server_proxy_port).parse()?),
        backend_address: Some(format!("127.0.0.1:{}", backend_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        backend_command: None,
        experimental_tls_session: false,
        tls_cert: None,
        tls_key: None,
    };

    let client_cfg_path = format!("client_http_ka_{}.toml", client_port);
    let server_cfg_path = format!("server_http_ka_{}.toml", server_proxy_port);
    std::fs::write(&client_cfg_path, toml::to_string(&client_config)?)?;
    std::fs::write(&server_cfg_path, toml::to_string(&server_config)?)?;

    let mut server_proxy = Command::new("oak_proxy/server/server")
        .args(["--config", &server_cfg_path, "--http"])
        .env("RUST_LOG", "debug")
        .spawn()?;

    tokio::time::sleep(Duration::from_secs(1)).await;

    let mut client_proxy = Command::new("oak_proxy/client/client")
        .args(["--config", &client_cfg_path, "--http"])
        .env("RUST_LOG", "debug")
        .spawn()?;

    tokio::time::sleep(Duration::from_secs(1)).await;

    let connect_result = async {
        let mut stream = TcpStream::connect(format!("127.0.0.1:{}", client_port)).await?;

        // Request #1 over keep-alive connection
        stream.write_all(b"GET /req1 HTTP/1.1\r\nHost: localhost\r\n\r\n").await?;
        let mut buf1 = vec![0; 1024];
        let n1 = stream.read(&mut buf1).await?;
        let resp1 = String::from_utf8_lossy(&buf1[..n1]);
        assert!(resp1.contains("HTTP/1.1 200 OK"));
        assert!(!resp1.contains("X-Oak-Attestation:"));

        // Request #2 over the exact same open keep-alive connection
        stream.write_all(b"POST /req2 HTTP/1.1\r\nHost: localhost\r\n\r\nbody").await?;
        let mut buf2 = vec![0; 1024];
        let n2 = stream.read(&mut buf2).await?;
        let resp2 = String::from_utf8_lossy(&buf2[..n2]);
        assert!(resp2.contains("HTTP/1.1 200 OK"));
        assert!(!resp2.contains("X-Oak-Attestation:"));

        Ok::<(), anyhow::Error>(())
    }
    .await;

    let _ = client_proxy.kill();
    let _ = server_proxy.kill();
    let _ = std::fs::remove_file(client_cfg_path);
    let _ = std::fs::remove_file(server_cfg_path);

    connect_result?;
    Ok(())
}

#[tokio::test]
async fn http_asymmetric_mode_test() -> anyhow::Result<()> {
    let backend_port = find_free_port();
    let server_proxy_port = find_free_port();
    let client_port = find_free_port();

    let backend = tokio::net::TcpListener::bind(format!("127.0.0.1:{}", backend_port)).await?;
    let _backend_task = tokio::spawn(async move {
        while let Ok((mut socket, _)) = backend.accept().await {
            tokio::spawn(async move {
                let mut buf = vec![0; 1024];
                if let Ok(n) = socket.read(&mut buf).await {
                    let req = String::from_utf8_lossy(&buf[..n]);
                    // Verify the backend does NOT receive X-Oak-Attestation when unattested
                    assert!(!req.contains("X-Oak-Attestation:"));
                    let _ = socket
                        .write_all(
                            b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 2\r\n\r\nOK",
                        )
                        .await;
                }
            });
        }
    });

    tokio::time::sleep(Duration::from_secs(1)).await;

    // Client proxy configured in default TCP mode (NO --http flag)
    let client_config = ClientConfig {
        mode: oak_proxy_lib::config::ProxyMode::Tcp,
        listen_address: Some(format!("127.0.0.1:{}", client_port).parse()?),
        server_proxy_url: Some(format!("ws://127.0.0.1:{}", server_proxy_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        attestation_output_file: None,
        experimental_tls_session: false,
        tls_ca: None,
    };

    // Server proxy configured in HTTP mode (--http flag enabled)
    let server_config = ServerConfig {
        mode: oak_proxy_lib::config::ProxyMode::Http,
        listen_address: Some(format!("127.0.0.1:{}", server_proxy_port).parse()?),
        backend_address: Some(format!("127.0.0.1:{}", backend_port).parse()?),
        attestation_generators: Vec::new(),
        attestation_verifiers: Vec::new(),
        keep_alive_interval: Duration::from_secs(10),
        backend_command: None,
        experimental_tls_session: false,
        tls_cert: None,
        tls_key: None,
    };

    let client_cfg_path = format!("client_tcp_asym_{}.toml", client_port);
    let server_cfg_path = format!("server_http_asym_{}.toml", server_proxy_port);
    std::fs::write(&client_cfg_path, toml::to_string(&client_config)?)?;
    std::fs::write(&server_cfg_path, toml::to_string(&server_config)?)?;

    let mut server_proxy = Command::new("oak_proxy/server/server")
        .args(["--config", &server_cfg_path, "--http"])
        .env("RUST_LOG", "debug")
        .spawn()?;

    tokio::time::sleep(Duration::from_secs(1)).await;

    let mut client_proxy = Command::new("oak_proxy/client/client")
        .args(["--config", &client_cfg_path]) // Notice: NO --http flag for client!
        .env("RUST_LOG", "debug")
        .spawn()?;

    tokio::time::sleep(Duration::from_secs(1)).await;

    let connect_result = async {
        let mut stream = TcpStream::connect(format!("127.0.0.1:{}", client_port)).await?;
        stream.write_all(b"GET /asymmetric HTTP/1.1\r\nHost: localhost\r\n\r\n").await?;
        let mut buf = Vec::new();
        stream.read_to_end(&mut buf).await?;
        Ok::<Vec<u8>, anyhow::Error>(buf)
    }
    .await;

    let _ = client_proxy.kill();
    let _ = server_proxy.kill();
    let _ = std::fs::remove_file(client_cfg_path);
    let _ = std::fs::remove_file(server_cfg_path);

    let buf = connect_result?;
    let response = String::from_utf8_lossy(&buf);
    println!("Asymmetric Response: {}", response);
    assert!(response.contains("HTTP/1.1 200 OK"));
    // Since client proxy was in TCP mode, it should NOT have spliced
    // X-Oak-Attestation onto the response!
    assert!(!response.contains("X-Oak-Attestation:"));

    Ok(())
}
