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

//! Private Information Retrieval example for Project Oak.
//!
//! This shows how an Oak Node can retrieve information from an external database and process
//! private queries from clients.
//!
//! Current example implementation uses a list of Santander Cycles in London as test database:
//! https://tfl.gov.uk/tfl/syndication/feeds/cycle-hire/livecyclehireupdates.xml
//!
//! Client sends an ID of some Point-Of-Interest and the Oak Node returns the detailed information
//! about the Point Of Interest (in our case a bike station) corresponding to the ID.

pub mod config;
pub mod proto {
    include!(concat!(
        env!("OUT_DIR"),
        "/oak.examples.trusted_information_retrieval.rs",
    ));
}
#[cfg(test)]
mod tests;

use config::get_database_url;
use database_proxy::get_database_entry;
use log::{debug, error};
use oak::grpc;
use prost::Message;
use proto::{
    GetPointOfInterestRequest, GetPointOfInterestResponse, TrustedInformationRetrieval,
    TrustedInformationRetrievalDispatcher,
};

/// Oak Node that connects to the database proxy Node.
pub struct TrustedInformationRetrievalNode {
    database_url: String,
}

/// A gRPC service implementation for the Private Information Retrieval example.
impl TrustedInformationRetrieval for TrustedInformationRetrievalNode {
    /// Get a point of interest based on requested id.
    fn get_point_of_interest(
        &mut self,
        request: GetPointOfInterestRequest,
    ) -> grpc::Result<GetPointOfInterestResponse> {
        debug!("Received request: {:?}", request);

        // Get requested database entry from the database proxy Node.
        let entry = get_database_entry(&request.id, &self.database_url).map_err(|error| {
            error!("Couldn't get point of interest: {:?}", error);
            error
        })?;

        // Decode point of interest.
        let point_of_interest = Message::decode(entry.value.as_bytes()).unwrap();
        Ok(GetPointOfInterestResponse {
            point_of_interest: Some(point_of_interest),
        })
    }
}

oak::entrypoint!(oak_main => |in_channel| {
    oak::logger::init_default();
    let config_map = oak::app_config_map(in_channel).expect("Couldn't read config map");
    let database_url = get_database_url(config_map).expect("Couldn't load database URL");
    let dispatcher = TrustedInformationRetrievalDispatcher::new(TrustedInformationRetrievalNode {
        database_url
    });
    let grpc_channel =
        oak::grpc::server::init("[::]:8080").expect("Couldn't create gRPC server pseudo-Node");
    oak::run_event_loop(dispatcher, grpc_channel);
});
