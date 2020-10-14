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
    application::Application,
    database::Database,
    proto::{
        trusted_database_client::TrustedDatabaseClient,
        trusted_database_server::{TrustedDatabase, TrustedDatabaseServer},
        GetPointOfInterestRequest, GetPointOfInterestResponse, ListPointsOfInterestRequest,
        ListPointsOfInterestResponse, PointOfInterestMap,
    },
};
use async_trait::async_trait;
use log::{debug, error, info};
use oak_abi::label::Label;
use prost::Message;
use tokio::task::JoinHandle;
use tonic::{
    metadata::MetadataValue,
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
                let err = tonic::Status::new(tonic::Code::Internal, "Empty database");
                error!("{:?}", err);
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
    _handle: JoinHandle<()>,
    client: TrustedDatabaseClient<tonic::transport::channel::Channel>,
}

impl NativeApplication {
    pub async fn start(database: &Database, port: u16) -> Self {
        info!("Running backend database");
        let handle = tokio::spawn(NativeApplication::create_server(
            database.points_of_interest.clone(),
            port,
        ));
        let client = NativeApplication::create_client(port).await;
        NativeApplication {
            _handle: handle,
            client,
        }
    }

    async fn create_server(database: PointOfInterestMap, port: u16) {
        let address = format!("[::]:{}", port)
            .parse()
            .expect("Couldn't parse address");
        let handler = TrustedDatabaseService {
            points_of_interest: database,
        };
        Server::builder()
            .add_service(TrustedDatabaseServer::new(handler))
            .serve(address)
            .await
            .expect("Couldn't start server");
    }

    async fn create_client(port: u16) -> TrustedDatabaseClient<tonic::transport::channel::Channel> {
        let address = format!("https://localhost:{}", port)
            .parse()
            .expect("Couldn't parse address");
        let channel = Channel::builder(address)
            .connect()
            .await
            .expect("Couldn't connect to Oak Application");

        let mut label = Vec::new();
        Label::public_untrusted()
            .encode(&mut label)
            .expect("Error encoding label");
        TrustedDatabaseClient::with_interceptor(channel, move |mut request: Request<()>| {
            request.metadata_mut().insert_bin(
                oak_abi::OAK_LABEL_GRPC_METADATA_KEY,
                MetadataValue::from_bytes(label.as_ref()),
            );
            Ok(request)
        })
    }
}

#[async_trait]
impl Application for NativeApplication {
    async fn send_request(&mut self, id: &str) -> Result<(), tonic::Status> {
        let request = Request::new(GetPointOfInterestRequest { id: id.to_string() });
        self.client.get_point_of_interest(request).await?;
        Ok(())
    }
}
