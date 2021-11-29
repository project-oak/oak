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

pub mod proto {
    tonic::include_proto!("tensorflow");
    pub mod serving {
        tonic::include_proto!("tensorflow.serving");
    }
}

pub use proto::serving::{prediction_service_client::PredictionServiceClient, PredictRequest};
use std::convert::TryFrom;
use tokio::{
    net::UnixStream,
    time::{sleep, Duration},
};
use tonic::transport::{Channel, Endpoint, Uri};
use tower::service_fn;

/// Connection to the prediction service that can be used for creating new clients.
pub struct BackendConnection {
    channel: Channel,
}

impl BackendConnection {
    /// Connects to the prediction service over UDS and returns the wrapped channel.
    pub async fn connect() -> Self {
        wait_for_socket(super::SOCKET).await;
        // Ignore this uri because UDS do not use it, but Endpoint requires a valid uri.
        let channel = Endpoint::try_from("http://[::]:50051")
            .expect("invalid uri")
            .connect_with_connector(service_fn(|_: Uri| {
                // Connect to a Unix Domain Socket
                UnixStream::connect(super::SOCKET)
            }))
            .await
            .expect("couldn't connect to backend socket");
        Self { channel }
    }

    /// Creates a new client.
    pub fn create_client(&self) -> PredictionServiceClient<Channel> {
        PredictionServiceClient::new(self.channel.clone())
    }
}

async fn wait_for_socket(socket: &str) {
    // Wait for up to 5 seconds for the socket to become visible.
    for _ in 0..50 {
        if std::path::Path::new(socket).exists() {
            return;
        }
        sleep(Duration::from_millis(100)).await;
    }
    panic!("socket not available in time");
}
