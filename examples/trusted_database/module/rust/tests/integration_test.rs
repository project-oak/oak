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

use anyhow::Context;
use assert_matches::assert_matches;
use maplit::hashmap;
use oak_abi::proto::oak::application::ConfigMap;
use oak_client::interceptors::label::LabelInterceptor;
use std::collections::HashMap;
use tonic::{service::interceptor::InterceptedService, transport::Channel};
use trusted_database_client::proto::{
    trusted_database_client::TrustedDatabaseClient, ListPointsOfInterestRequest,
    ListPointsOfInterestResponse, Location, PointOfInterest,
};

const MAIN_MODULE_NAME: &str = "app";
const MAIN_ENTRYPOINT_NAME: &str = "oak_main";
const MAIN_MODULE_MANIFEST: &str = "../../module/rust/Cargo.toml";

const XML_DATABASE: &str = r#"<?xml version="1.0" encoding="utf-8"?><stations lastUpdate="1590775020879" version="2.0">
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

fn build_wasm() -> anyhow::Result<HashMap<String, Vec<u8>>> {
    Ok(hashmap! {
        MAIN_MODULE_NAME.to_owned() => oak_tests::compile_rust_wasm(MAIN_MODULE_MANIFEST, oak_tests::Profile::Release).context("Couldn't compile main module")?,
    })
}

async fn list_points_of_interest(
    client: &mut TrustedDatabaseClient<InterceptedService<Channel, LabelInterceptor>>,
    latitude: f32,
    longitude: f32,
) -> Result<tonic::Response<ListPointsOfInterestResponse>, tonic::Status> {
    let request = ListPointsOfInterestRequest {
        location: Some(Location {
            latitude_degrees: latitude,
            longitude_degrees: longitude,
        }),
    };
    client.list_points_of_interest(request).await
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn test_trusted_database() {
    env_logger::init();

    // Send test database as a start-of-day config map.
    let config_map = ConfigMap {
        items: hashmap! {"database".to_string() => XML_DATABASE.as_bytes().to_vec()},
    };
    let wasm_modules = build_wasm().expect("Couldn't build wasm modules");
    let permissions = oak_runtime::permissions::PermissionsConfiguration {
        allow_grpc_server_nodes: true,
        allow_log_nodes: true,
        ..Default::default()
    };
    let config = oak_tests::runtime_config_wasm(
        wasm_modules,
        MAIN_MODULE_NAME,
        MAIN_ENTRYPOINT_NAME,
        config_map,
        permissions,
        oak_runtime::SignatureTable::default(),
    );
    let runtime =
        oak_runtime::configure_and_run(config).expect("Couldn't configure runtime with test wasm");

    let (channel, interceptor) = oak_tests::public_channel_and_interceptor().await;
    let mut client = TrustedDatabaseClient::with_interceptor(channel, interceptor);

    // Test nearest point of interest.
    let result = list_points_of_interest(&mut client, 0.0, 4.0).await;
    assert_matches!(result, Ok(_));
    let got = result.unwrap().into_inner();
    let want = ListPointsOfInterestResponse {
        point_of_interest: Some(PointOfInterest {
            name: "Opened station 1".to_string(),
            location: Some(Location {
                latitude_degrees: 0.0,
                longitude_degrees: 0.0,
            }),
        }),
    };
    assert_eq!(got, want);

    // Second test is necessary to show that `list_points_of_interest` is not always returning the
    // same result.
    let result = list_points_of_interest(&mut client, 6.0, 0.0).await;
    assert_matches!(result, Ok(_));
    let got = result.unwrap().into_inner();
    let want = ListPointsOfInterestResponse {
        point_of_interest: Some(PointOfInterest {
            name: "Opened station 2".to_string(),
            location: Some(Location {
                latitude_degrees: 10.0,
                longitude_degrees: 0.0,
            }),
        }),
    };
    assert_eq!(got, want);

    runtime.stop();
}
