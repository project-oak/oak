//
// Copyright 2020 The Project Oak Authors
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

use crate::{
    application::ApplicationClient,
    database::Database,
    proto::{
        trusted_database_client::TrustedDatabaseClient,
        trusted_database_server::{TrustedDatabase, TrustedDatabaseServer},
        GetPointOfInterestRequest, GetPointOfInterestResponse, ListPointsOfInterestRequest,
        ListPointsOfInterestResponse, PointOfInterestMap,
    },
};
use anyhow::Context;
use async_trait::async_trait;
use futures_util::FutureExt;
use log::{debug, info, warn};
use oak_abi::label::Label;
use oak_client::interceptors::label::LabelInterceptor;
use tokio::sync::oneshot;
use tonic::{
    service::interceptor::InterceptedService,
    transport::{Channel, Server},
    Request, Response, Status,
};

pub struct TrustedDatabaseService {
    points_of_interest: PointOfInterestMap,
}

#[tonic::async_trait]
impl TrustedDatabase for TrustedDatabaseService {
    // Find Point Of Interest based on id.
    async fn get_point_of_interest(
        &self,
        request: Request<GetPointOfInterestRequest>,
    ) -> Result<Response<GetPointOfInterestResponse>, Status> {
        debug!("Received request: {:?}", request);
        match self.points_of_interest.entries.get(&request.get_ref().id) {
            Some(point) => {
                debug!("Found Point Of Interest: {:?}", point);
                Ok(Response::new(GetPointOfInterestResponse {
                    point_of_interest: Some(point.clone()),
                }))
            }
            None => {
                let err = tonic::Status::new(tonic::Code::NotFound, "ID not found");
                warn!("{:?}", err);
                Err(err)
            }
        }
    }

    async fn list_points_of_interest(
        &self,
        _request: Request<ListPointsOfInterestRequest>,
    ) -> Result<Response<ListPointsOfInterestResponse>, Status> {
        unimplemented!();
    }
}

pub struct NativeApplication {
    notification_sender: oneshot::Sender<()>,
    client: TrustedDatabaseClient<InterceptedService<Channel, LabelInterceptor>>,
}

impl NativeApplication {
    pub async fn start(database: &Database, port: u16) -> Self {
        info!("Running native application");
        let (notification_sender, notification_receiver) = oneshot::channel::<()>();
        tokio::spawn(NativeApplication::create_server(
            database.points_of_interest.clone(),
            port,
            notification_receiver,
        ));
        let client = NativeApplication::create_client(port).await;
        NativeApplication {
            notification_sender,
            client,
        }
    }

    pub fn stop(self) -> anyhow::Result<()> {
        self.notification_sender
            .send(())
            .ok()
            .context("Couldn't stop native application")
    }

    async fn create_server(
        database: PointOfInterestMap,
        port: u16,
        termination_notification_receiver: oneshot::Receiver<()>,
    ) {
        let address = format!("[::]:{}", port)
            .parse()
            .expect("Couldn't parse address");
        let handler = TrustedDatabaseService {
            points_of_interest: database,
        };
        Server::builder()
            .add_service(TrustedDatabaseServer::new(handler))
            .serve_with_shutdown(address, termination_notification_receiver.map(drop))
            .await
            .expect("Couldn't start server");
    }

    async fn create_client(
        port: u16,
    ) -> TrustedDatabaseClient<InterceptedService<Channel, LabelInterceptor>> {
        let address = format!("https://localhost:{}", port)
            .parse()
            .expect("Couldn't parse address");
        let channel = Channel::builder(address)
            .connect()
            .await
            .expect("Couldn't connect to Oak Application");
        let label = Label::public_untrusted();
        let interceptor =
            LabelInterceptor::create(&label).expect("Couldn't create gRPC interceptor");

        TrustedDatabaseClient::with_interceptor(channel, interceptor)
    }
}

#[async_trait]
impl ApplicationClient for NativeApplication {
    /// Sends test requests to the native application. Returns `()` since the value of the request
    /// is not needed for current benchmark implementation.
    async fn send_request(&mut self, id: &str) -> Result<(), tonic::Status> {
        let request = Request::new(GetPointOfInterestRequest { id: id.to_string() });
        self.client.get_point_of_interest(request).await?;
        Ok(())
    }
}
