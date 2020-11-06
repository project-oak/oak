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

//! Trusted Database Handler Node.
//!
//! In the current implementation clients send their location coordinates (latitude and longitude)
//! and the Handler Node returns the location of the closest Point Of Interest.
//!
//! The Handler Node searches for the closest Point Of Interest in the database received from the
//! Main Node.

use crate::proto::oak::examples::trusted_database::{
    GetPointOfInterestRequest, GetPointOfInterestResponse, ListPointsOfInterestRequest,
    ListPointsOfInterestResponse, Location, PointOfInterestMap, TrustedDatabase,
    TrustedDatabaseCommand, TrustedDatabaseDispatcher,
};
use log::{debug, error, warn};
use oak::{
    grpc,
    io::{Receiver, ReceiverExt},
};

// Error messages.
const NO_LOCATION_ERROR: &str = "Location is not specified";
const ID_NOT_FOUND_ERROR: &str = "ID not found";
const EMPTY_DATABASE_ERROR: &str = "Empty database";

/// Oak Node that contains a copy of the database.
pub struct TrustedDatabaseHandlerNode {
    points_of_interest: PointOfInterestMap,
}

oak::impl_dispatcher!(impl TrustedDatabaseHandlerNode : TrustedDatabaseDispatcher);

/// A gRPC service implementation for the Private Information Retrieval example.
impl TrustedDatabase for TrustedDatabaseHandlerNode {
    // Find Point Of Interest based on id.
    fn get_point_of_interest(
        &mut self,
        request: GetPointOfInterestRequest,
    ) -> grpc::Result<GetPointOfInterestResponse> {
        debug!("Received request: {:?}", request);
        match self.points_of_interest.entries.get(&request.id) {
            Some(point) => {
                debug!("Found Point Of Interest: {:?}", point);
                Ok(GetPointOfInterestResponse {
                    point_of_interest: Some(point.clone()),
                })
            }
            None => {
                let err = grpc::build_status(grpc::Code::NotFound, &ID_NOT_FOUND_ERROR);
                error!("{:?}", err);
                Err(err)
            }
        }
    }

    /// Find the nearest Point Of Interest based on linear search in the database.
    fn list_points_of_interest(
        &mut self,
        request: ListPointsOfInterestRequest,
    ) -> grpc::Result<ListPointsOfInterestResponse> {
        debug!("Received request: {:?}", request);
        let request_location = request.location.ok_or_else(|| {
            let err = grpc::build_status(grpc::Code::InvalidArgument, &NO_LOCATION_ERROR);
            warn!("{:?}", err);
            err
        })?;
        let nearest_point = self.points_of_interest.entries.values().fold(
            (None, f32::MAX),
            |(current_closest_point, current_closest_point_distance), point| {
                let point_location = point
                    .location
                    .as_ref()
                    .expect("Non-existing location")
                    .clone();
                let distance = distance(request_location.clone(), point_location);
                if distance < current_closest_point_distance {
                    (Some(point.clone()), distance)
                } else {
                    (current_closest_point, current_closest_point_distance)
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
                let err = grpc::build_status(grpc::Code::Internal, &EMPTY_DATABASE_ERROR);
                error!("{:?}", err);
                Err(err)
            }
        }
    }
}

// Earth radius in kilometers.
const EARTH_RADIUS: f32 = 6371.0_f32;

/// Returns a distance (in kilometers) between two locations using the Haversine formula
/// (ignoring height variations):
/// https://en.wikipedia.org/wiki/Haversine_formula
pub fn distance(first: Location, second: Location) -> f32 {
    let first_latitude_radians = first.latitude_degrees.to_radians();
    let second_latitude_radians = second.latitude_degrees.to_radians();

    let latitude_difference_radians =
        (first.latitude_degrees - second.latitude_degrees).to_radians();
    let longitude_difference_radians =
        (first.longitude_degrees - second.longitude_degrees).to_radians();

    let central_angle = 2.0
        * ((latitude_difference_radians / 2.0).sin().powi(2)
            + (first_latitude_radians.cos()
                * second_latitude_radians.cos()
                * (longitude_difference_radians / 2.0).sin().powi(2)))
        .sqrt()
        .asin();

    // Compute distance.
    EARTH_RADIUS * central_angle
}

oak::entrypoint!(handler_oak_main<TrustedDatabaseCommand> => |command_receiver: Receiver<TrustedDatabaseCommand>| {
    oak::logger::init_default();

    // Receive command.
    let command: TrustedDatabaseCommand =
        command_receiver.receive().expect("Couldn't receive command");
    let receiver = command.invocation_receiver.expect("Couldn't receive gRPC invocation receiver");

    // Run event loop and handle incoming invocations.
    let node = TrustedDatabaseHandlerNode { points_of_interest: command.points_of_interest.expect("No database entries") };
    let invocation_receiver = receiver.receiver.expect("Empty gRPC invocation receiver");
    // The event loop only runs once because the `Main` Node sends a single invocation.
    oak::run_command_loop(node, invocation_receiver.iter());
});
