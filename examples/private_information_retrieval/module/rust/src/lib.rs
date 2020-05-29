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
        "/oak.examples.private_information_retrieval.rs"
    ));
}

mod database;
#[cfg(test)]
mod tests;

use database::load_database;
use log::{debug, error};
use oak::grpc;
use proto::{
    Location, PointOfInterest, PrivateInformationRetrieval, PrivateInformationRetrievalDispatcher,
};

/// Oak Node that contains an in-memory database of Points Of Interest.
pub struct PrivateInformationRetrievalNode {
    points_of_interest: Vec<PointOfInterest>,
}

impl PrivateInformationRetrievalNode {
    /// Returns a Euclidean distance between two locations.
    fn distance(first: Location, second: Location) -> f32 {
        let x = first.latitude - second.latitude;
        let y = first.longitude - second.longitude;
        (x * x + y * y).sqrt()
    }
}

/// A gRPC service implementation for the Private Information Retrieval example.
impl PrivateInformationRetrieval for PrivateInformationRetrievalNode {
    /// Find the nearest Point Of Interest based on linear search in the database.
    fn get_nearest_point_of_interest(
        &mut self,
        location: Location,
    ) -> grpc::Result<PointOfInterest> {
        debug!("Received location: {:?}", location);
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
                debug!("Sending the nearest Point Of Interest: {:?}", point);
                Ok(point)
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
    let dispatcher = PrivateInformationRetrievalDispatcher::new(PrivateInformationRetrievalNode {
        points_of_interest,
    });
    oak::run_event_loop(dispatcher, in_channel);
});

oak::entrypoint!(grpc_oak_main => |in_channel| {
    oak::logger::init_default();
    let points_of_interest = load_database(in_channel).expect("Couldn't load database");
    let dispatcher = PrivateInformationRetrievalDispatcher::new(PrivateInformationRetrievalNode {
        points_of_interest,
    });
    let grpc_channel = oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
    oak::run_event_loop(dispatcher, grpc_channel);
});
