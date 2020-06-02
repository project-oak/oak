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
//! This shows how an Oak Node can host an in-memory database and process private queries from
//! clients.
//!
//! Current example implementation uses a list of Santander Cycles in London as test database:
//! https://tfl.gov.uk/tfl/syndication/feeds/cycle-hire/livecyclehireupdates.xml
//!
//! Clients send their location coordinates (latitude and longitude) and the Oak Node returns the
//! location of the closest Point Of Interest (in our case a bike station).

mod proto {
    include!(concat!(
        env!("OUT_DIR"),
        "/oak.examples.trusted_information_retrieval.rs"
    ));
}

mod database;
#[cfg(test)]
mod tests;

use database::load_database;
use log::{debug, error};
use oak::grpc;
use proto::{
    ListPointsOfInterestRequest, ListPointsOfInterestResponse, Location, PointOfInterest,
    TrustedInformationRetrieval, TrustedInformationRetrievalDispatcher,
};

/// Oak Node that contains an in-memory database of Points Of Interest.
pub struct TrustedInformationRetrievalNode {
    points_of_interest: Vec<PointOfInterest>,
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
            let err = "Location is not specified".to_string();
            error!("Bad request: {:?}", err);
            grpc::build_status(grpc::Code::InvalidArgument, &err)
        })?;
        let nearest_point = self.points_of_interest.iter().fold(
            (None, f32::MAX),
            |(closest_point, min_distance), point| {
                let point_location = point.location.clone().expect("Non-existing location");
                let distance = Self::distance(location.clone(), point_location);
                if distance < min_distance {
                    (Some(point.clone()), distance)
                } else {
                    (closest_point, min_distance)
                }
            },
        );
        match nearest_point.0 {
            Some(point) => {
                debug!("Found the nearest Point Of Interest: {:?}", point);
                Ok(ListPointsOfInterestResponse {
                    point_of_interest: Some(point),
                })
            }
            None => {
                let err = "Empty database".to_string();
                error!("Couldn't find the nearest Point Of Interest: {:?}", err);
                Err(grpc::build_status(grpc::Code::InvalidArgument, &err))
            }
        }
    }
}

oak::entrypoint!(oak_main => |in_channel| {
    oak::logger::init_default();
    let points_of_interest = load_database(in_channel).expect("Couldn't load database");
    let dispatcher = TrustedInformationRetrievalDispatcher::new(TrustedInformationRetrievalNode {
        points_of_interest,
    });
    oak::run_event_loop(dispatcher, in_channel);
});

oak::entrypoint!(grpc_oak_main => |in_channel| {
    oak::logger::init_default();
    let points_of_interest = load_database(in_channel).expect("Couldn't load database");
    let dispatcher = TrustedInformationRetrievalDispatcher::new(TrustedInformationRetrievalNode {
        points_of_interest,
    });
    let grpc_channel = oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
    oak::run_event_loop(dispatcher, grpc_channel);
});
