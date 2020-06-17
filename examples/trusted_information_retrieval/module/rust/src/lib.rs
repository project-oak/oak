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
//! Clients send their location coordinates (latitude and longitude) and the Oak Node returns the
//! location of the closest Point Of Interest (in our case a bike station).

pub mod config;
pub mod proto {
    include!(concat!(
        env!("OUT_DIR"),
        "/oak.examples.trusted_information_retrieval.rs"
    ));
}
#[cfg(test)]
mod tests;

use anyhow::{anyhow, Context};
use config::get_database_url;
use log::{debug, error, warn};
use oak::grpc;
use oak_abi::label::Label;
use proto::{
    DatabaseClient, ListDatabaseEntriesRequest, ListPointsOfInterestRequest,
    ListPointsOfInterestResponse, Location, PointOfInterest, TrustedInformationRetrieval,
    TrustedInformationRetrievalDispatcher,
};

/// Expected number of database entries per request.
const DATABASE_PAGE_SIZE: u32 = 5;

/// Oak Node that connects to an external database of Points Of Interest.
pub struct TrustedInformationRetrievalNode {
    database_url: String,
}

impl TrustedInformationRetrievalNode {
    /// Returns a distance (in kilometers) between two locations using the Haversine formula
    /// (ignoring height variations):
    /// https://en.wikipedia.org/wiki/Haversine_formula
    fn distance(first: Location, second: Location) -> f32 {
        let first_latitude_radians = first.latitude.to_radians();
        let second_latitude_radians = second.latitude.to_radians();

        let latitude_difference_radians = (first.latitude - second.latitude).to_radians();
        let longitude_difference_radians = (first.longitude - second.longitude).to_radians();

        let central_angle = 2.0
            * ((latitude_difference_radians / 2.0).sin().powi(2)
                + (first_latitude_radians.cos()
                    * second_latitude_radians.cos()
                    * (longitude_difference_radians / 2.0).sin().powi(2)))
            .sqrt()
            .asin();

        // Earth radius in kilometers.
        let earth_radius = 6371.0_f32;

        // Compute distance.
        earth_radius * central_angle
    }

    /// Create a gRPC client pseudo-Node.
    fn get_grpc_client(&self) -> anyhow::Result<DatabaseClient> {
        oak::grpc::client::Client::new_with_label(
            &oak::node_config::grpc_client(&self.database_url),
            &Label::public_untrusted(),
        )
        .map(DatabaseClient)
        .context("Couldn't create a gRPC client")
    }

    /// Load a database subset defined by `offset` and the number of requested elements
    /// (`page_size`).
    fn list_database_entries(
        &self,
        offset: u32,
        page_size: u32,
    ) -> anyhow::Result<Vec<PointOfInterest>> {
        let request = ListDatabaseEntriesRequest {
            offset: offset as i32,
            page_size: page_size as i32,
        };
        self.get_grpc_client()?
            .list_database_entries(request)
            .map(|response| {
                response
                    .entries
                    .iter()
                    // Filter out uninstalled, closed and removed stations, and stations with no
                    // bikes.
                    .filter(|station| {
                        station.installed
                            && !station.locked
                            && station.removal_date.is_empty()
                            && station.number_of_bikes > 0
                    })
                    .map(|station| PointOfInterest {
                        name: station.name.to_string(),
                        location: Some(Location {
                            latitude: station.latitude_degrees,
                            longitude: station.longitude_degrees,
                        }),
                    })
                    .collect()
            })
            .map_err(|error| anyhow!("gRPC send error: {:?}", error))
    }
}

/// A gRPC service implementation for the Private Information Retrieval example.
impl TrustedInformationRetrieval for TrustedInformationRetrievalNode {
    /// Find the nearest Point Of Interest based on linear search in the database.
    fn list_points_of_interest(
        &mut self,
        request: ListPointsOfInterestRequest,
    ) -> grpc::Result<ListPointsOfInterestResponse> {
        debug!("Received request: {:?}", request);
        let location = request.location.ok_or_else(|| {
            let status =
                grpc::build_status(grpc::Code::InvalidArgument, "Location is not specified");
            warn!("Bad request: {:?}", status);
            status
        })?;

        // Request entries from the database until the last entry page is reached.
        let mut current_offset = 0;
        let mut nearest_point = None;
        let mut last = false;
        while !last {
            let points_of_interest = self
                .list_database_entries(current_offset, DATABASE_PAGE_SIZE)
                .map_err(|error| {
                    let status = grpc::build_status(grpc::Code::Unavailable, "");
                    error!("Couldn't get database entries: {:?}, {:?}", error, status);
                    status
                })?;

            // Find the nearest point of interest.
            nearest_point = points_of_interest
                .iter()
                .fold(
                    (nearest_point, f32::MAX),
                    |(current_nearest_point, min_distance), point| {
                        let point_location = point.location.clone().expect("Non-existing location");
                        let distance = Self::distance(location.clone(), point_location);
                        if distance < min_distance {
                            (Some(point.clone()), distance)
                        } else {
                            (current_nearest_point, min_distance)
                        }
                    },
                )
                .0;

            // If the response contains less entries than expected, then it's the last database
            // page.
            if points_of_interest.len() < DATABASE_PAGE_SIZE as usize {
                last = true;
            }
            current_offset += DATABASE_PAGE_SIZE;
        }

        nearest_point
            .map(|point| {
                debug!("Found the nearest Point Of Interest: {:?}", point);
                ListPointsOfInterestResponse {
                    point_of_interest: Some(point),
                }
            })
            .ok_or({
                let status = grpc::build_status(grpc::Code::NotFound, "No open stations");
                error!("Couldn't find the nearest Point Of Interest: {:?}", status);
                status
            })
    }
}

oak::entrypoint!(oak_main => |in_channel| {
    oak::logger::init_default();
    let database_url = get_database_url(in_channel).expect("Couldn't load database URL");
    let dispatcher = TrustedInformationRetrievalDispatcher::new(TrustedInformationRetrievalNode {
        database_url
    });
    oak::run_event_loop(dispatcher, in_channel);
});

oak::entrypoint!(grpc_oak_main => |in_channel| {
    oak::logger::init_default();
    let database_url = get_database_url(in_channel).expect("Couldn't load database URL");
    let dispatcher = TrustedInformationRetrievalDispatcher::new(TrustedInformationRetrievalNode {
        database_url
    });
    let grpc_channel =
        oak::grpc::server::init("[::]:8080").expect("Couldn't create gRPC server pseudo-Node");
    oak::run_event_loop(dispatcher, grpc_channel);
});
