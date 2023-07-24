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
            #![allow(clippy::return_self_not_must_use)]
            tonic::include_proto!("oak.containers");
        }
        pub mod session {
            pub mod v1 {
                #![allow(clippy::return_self_not_must_use)]
                tonic::include_proto!("oak.session.v1");
            }
        }
    }
}

use anyhow::Context;
use oak_containers_orchestrator_client::LauncherClient;
use proto::oak::containers::{
    orchestrator_server::{Orchestrator, OrchestratorServer},
    GetApplicationConfigResponse, NotifyAppReadyRequest,
};
use tokio::net::UnixListener;
use tokio_stream::wrappers::UnixListenerStream;
use tonic::{transport::Server, Request, Response};

pub struct ServiceImplementation {
    application_config: Vec<u8>,
    launcher_client: LauncherClient,
}

#[tonic::async_trait]
impl Orchestrator for ServiceImplementation {
    async fn get_application_config(
        &self,
        _request: Request<()>,
    ) -> Result<Response<GetApplicationConfigResponse>, tonic::Status> {
        Ok(tonic::Response::new(GetApplicationConfigResponse {
            config: self.application_config.clone(),
        }))
    }

    async fn notify_app_ready(
        &self,
        request: Request<NotifyAppReadyRequest>,
    ) -> Result<Response<()>, tonic::Status> {
        self.launcher_client
            .notify_app_ready(request.into_inner().listening_port as u16)
            .await
            .map_err(|err| tonic::Status::internal(format!("couldn't send notification: {err}")))?;
        Ok(tonic::Response::new(()))
    }
}

pub async fn create<P>(
    socket_address: P,
    application_config: Vec<u8>,
    launcher_client: LauncherClient,
) -> Result<(), anyhow::Error>
where
    P: AsRef<std::path::Path>,
{
    let service_instance = ServiceImplementation {
        application_config,
        launcher_client,
    };
    let uds =
        UnixListener::bind(socket_address).context("could not bind to the supplied address")?;
    let uds_stream = UnixListenerStream::new(uds);

    Server::builder()
        .add_service(OrchestratorServer::new(service_instance))
        .serve_with_incoming(uds_stream)
        .await?;

    Ok(())
}
