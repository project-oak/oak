//
// Copyright 2023 The Project Oak Authors
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

pub mod proto {
    pub mod oak {
        pub mod functions {
            tonic::include_proto!("oak.functions");
        }
    }
}

use std::{
    fs,
    net::{IpAddr, Ipv4Addr, SocketAddr},
    sync::Arc,
    time::Duration,
};

use oak_crypto::encryptor::EncryptionKeyProvider;
use oak_functions_containers_app::serve;
use oak_functions_service::proto::oak::functions::InitializeRequest;
use opentelemetry::metrics::{noop::NoopMeterProvider, MeterProvider};
use tokio::net::TcpListener;
use tonic::{codec::CompressionEncoding, transport::Endpoint};

use crate::proto::oak::functions::oak_functions_client::OakFunctionsClient;

#[tokio::test]
async fn test_lookup() {
    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup")
        .expect("Failed to build Wasm module");

    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await.unwrap();
    let addr = listener.local_addr().unwrap();

    let server_handle = tokio::spawn(serve(
        listener,
        Arc::new(EncryptionKeyProvider::generate()),
        NoopMeterProvider::new().meter(""),
    ));

    let mut oak_functions_client: OakFunctionsClient<tonic::transport::channel::Channel> = {
        let channel = Endpoint::from_shared(format!("http://{addr}"))
            .expect("couldn't form channel")
            .connect_timeout(Duration::from_secs(120))
            .connect()
            .await
            .expect("couldn't connect to trusted app");
        OakFunctionsClient::new(channel).send_compressed(CompressionEncoding::Gzip)
    };

    let _ = oak_functions_client
        .initialize(InitializeRequest {
            constant_response_size: 1000,
            wasm_module: fs::read(wasm_path).expect("failed to read wasm module"),
        })
        .await
        .expect("failed to initialize Oak Functions");

    server_handle.abort();
    let _ = server_handle.await;
}
