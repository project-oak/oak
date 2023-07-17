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

mod proto {
    pub mod oak {
        pub mod containers {
            pub mod example {
                tonic::include_proto!("oak.containers.example");
            }
        }
    }
}

use self::proto::oak::containers::example::{
    trusted_application_server::{TrustedApplication, TrustedApplicationServer},
    HelloRequest, HelloResponse,
};
use anyhow::anyhow;
use tokio_stream::{self as stream};

#[derive(Default)]
struct TrustedApplicationImplementation {
    application_config: Vec<u8>,
}

#[tonic::async_trait]
impl TrustedApplication for TrustedApplicationImplementation {
    async fn hello(
        &self,
        request: tonic::Request<HelloRequest>,
    ) -> Result<tonic::Response<HelloResponse>, tonic::Status> {
        let name = request.into_inner().name;
        let greeting: String = format!("Hello from the trusted side, {}! Btw, the Trusted App has a config with a length of {} bytes.", name, self.application_config.len());
        let response = tonic::Response::new(HelloResponse { greeting });
        Ok(response)
    }
}

pub async fn create(cid: u32, port: u32, application_config: Vec<u8>) -> Result<(), anyhow::Error> {
    // When building a gRPC server, tonic expects an async stream that yields
    // multiple incoming connections, each representing an individual client.
    // This case is a bit different: there will only be one client, the
    // untrusted app.
    let incoming = {
        // Connect to the untrusted app.
        let stream_with_untrusted_app = tokio_vsock::VsockStream::connect(cid, port).await;
        // Construct a stream that immediately yields just this connection.
        stream::once(stream_with_untrusted_app)
    };

    tonic::transport::Server::builder()
        .add_service(TrustedApplicationServer::new(
            TrustedApplicationImplementation { application_config },
        ))
        // the server is served explicitly with no shutdown, since otherwise it
        // shuts down as soon as the incoming stream yields no more new
        // connections even if existing connections are still active.
        // TODO(#4166): Replace this connection with an ordinary network
        // connection.
        .serve_with_incoming_shutdown(incoming, None)
        .await
        .map_err(|error| anyhow!("server error: {:?}", error))
}
