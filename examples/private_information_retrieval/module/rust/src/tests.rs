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
    database::parse_database,
    proto::{ListPointsOfInterestResponse, ListPointsOfInterestRequest, Location, PointOfInterest},
    PrivateInformationRetrievalNode,
};
use assert_matches::assert_matches;
use maplit::hashmap;
use oak::grpc;
use oak_abi::{proto::oak::application::ConfigMap, OakStatus};
use oak_runtime::io::Encodable;

const MODULE_CONFIG_NAME: &str = "private_information_retrieval";

const XML_DATABASE: &str =
r#"<?xml version="1.0" encoding="utf-8"?><stations lastUpdate="1590775020879" version="2.0">
    <station>
        <id>1</id>
        <name>Uninstalled station</name>
        <terminalName>1</terminalName>
        <lat>-10.0</lat>
        <long>-10.0</long>
        <installed>false</installed>
        <locked>false</locked>
        <installDate/>
        <removalDate/>
        <temporary>false</temporary>
        <nbBikes>1</nbBikes>
        <nbEmptyDocks>1</nbEmptyDocks>
        <nbDocks>1</nbDocks>
    </station>
    <station>
        <id>2</id>
        <name>Locked station</name>
        <terminalName>2</terminalName>
        <lat>0.0</lat>
        <long>-10.0</long>
        <installed>true</installed>
        <locked>true</locked>
        <installDate>0</installDate>
        <removalDate/>
        <temporary>false</temporary>
        <nbBikes>1</nbBikes>
        <nbEmptyDocks>1</nbEmptyDocks>
        <nbDocks>1</nbDocks>
    </station>
    <station>
        <id>3</id>
        <name>Opened station 1</name>
        <terminalName>3</terminalName>
        <lat>0.0</lat>
        <long>0.0</long>
        <installed>true</installed>
        <locked>false</locked>
        <installDate>0</installDate>
        <removalDate/>
        <temporary>false</temporary>
        <nbBikes>1</nbBikes>
        <nbEmptyDocks>1</nbEmptyDocks>
        <nbDocks>1</nbDocks>
    </station>
    <station>
        <id>4</id>
        <name>Opened station 2</name>
        <terminalName>4</terminalName>
        <lat>10.0</lat>
        <long>0.0</long>
        <installed>true</installed>
        <locked>false</locked>
        <installDate>0</installDate>
        <removalDate/>
        <temporary>false</temporary>
        <nbBikes>1</nbBikes>
        <nbEmptyDocks>1</nbEmptyDocks>
        <nbDocks>1</nbDocks>
    </station>
</stations>"#;

fn send_database(
    runtime: &oak_runtime::RuntimeProxy,
    entry_handle: oak_abi::Handle,
    database: Vec<u8>,
) -> Result<(), OakStatus> {
    let config_map = ConfigMap {
        items: hashmap! {"database".to_string() => database},
    };
    runtime.channel_write(entry_handle, config_map.encode()?)
}

fn submit_sample(
    runtime: &oak_runtime::RuntimeProxy,
    entry_handle: oak_abi::Handle,
    latitude: f32,
    longitude: f32,
) -> grpc::Result<ListPointsOfInterestResponse> {
    let req = ListPointsOfInterestRequest {
        location: Some(Location {
            latitude,
            longitude,
        }),
    };
    oak_tests::grpc_request(
        &runtime,
        entry_handle,
        "/oak.examples.private_information_retrieval.PrivateInformationRetrieval/ListPointsOfInterest",
        &req,
    )
}

#[test]
fn test_parse_database() {
    let database = parse_database(&XML_DATABASE.as_bytes().to_vec());
    assert_matches!(database, Ok(_));
    // Check that locked and uninstalled stations are filtered out.
    assert_eq!(database.unwrap().len(), 2);
}

#[test]
fn test_private_information_retrieval() {
    simple_logger::init_by_env();

    let (runtime, entry_handle) = oak_tests::run_single_module_default(MODULE_CONFIG_NAME)
        .expect("Unable to configure runtime with test wasm!");

    // Send test database.
    assert_matches!(
        send_database(&runtime, entry_handle, XML_DATABASE.as_bytes().to_vec(),),
        Ok(_)
    );

    // Test nearest point of interest
    assert_eq!(
        submit_sample(&runtime, entry_handle, 4.0, -10.0,),
        Ok(ListPointsOfInterestResponse {
            point_of_interest: Some(PointOfInterest {
                name: "Opened station 1".to_string(),
                location: Some(Location {
                    latitude: 0.0,
                    longitude: 0.0,
                }),
            }),
        }),
    );
    assert_eq!(
        submit_sample(&runtime, entry_handle, 9.0, -10.0,),
        Ok(ListPointsOfInterestResponse {
            point_of_interest: Some(PointOfInterest {
                name: "Opened station 2".to_string(),
                location: Some(Location {
                    latitude: 10.0,
                    longitude: 0.0,
                }),
            }),
        }),
    );
}

fn distance(first: (f32, f32), second: (f32, f32)) -> f32 {
    PrivateInformationRetrievalNode::distance(
        Location {
            latitude: first.0,
            longitude: first.1,
        },
        Location {
            latitude: second.0,
            longitude: second.1,
        },
    )
}

#[test]
fn test_distance() {
    assert_eq!(
        distance((0.0, 0.0), (0.0, 0.0)),
        0.0,
    );
    assert_eq!(
        distance((0.0, 0.0), (10.0, 10.0)),
        1568.5204,
    );
    assert_eq!(
        distance((10.0, 10.0), (-10.0, -10.0)),
        3137.0413,
    );
    assert_eq!(
        distance((0.0, 0.0), (0.0, 180.0)),
        20015.088,
    );
    assert_eq!(
        distance((90.0, 0.0), (-90.0, 180.0)),
        20015.088,
    );
}
