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

use assert_matches::assert_matches;
use maplit::hashmap;
use oak_abi::{proto::oak::application::ConfigMap, OakStatus};
use oak_runtime::io::Encodable;
use trusted_information_retrieval_client::proto::{
    trusted_information_retrieval_client::TrustedInformationRetrievalClient,
    ListPointsOfInterestRequest, ListPointsOfInterestResponse, Location,
};

const MODULE_CONFIG_NAME: &str = "trusted_information_retrieval";

const CONFIG_FILE: &str = r#"
database_url = "https://localhost:8888"
"#;

fn send_config(
    runtime: &oak_runtime::RuntimeProxy,
    entry_handle: oak_abi::Handle,
    config_file: Vec<u8>,
) -> Result<(), OakStatus> {
    let config_map = ConfigMap {
        items: hashmap! {"config".to_string() => config_file},
    };
    runtime.channel_write(entry_handle, config_map.encode()?)
}

async fn submit_sample(
    client: &mut TrustedInformationRetrievalClient<tonic::transport::Channel>,
    latitude: f32,
    longitude: f32,
) -> Result<tonic::Response<ListPointsOfInterestResponse>, tonic::Status> {
    let req = ListPointsOfInterestRequest {
        location: Some(Location {
            latitude,
            longitude,
        }),
    };
    client.list_points_of_interest(req).await
}

#[tokio::test(core_threads = 2)]
async fn test_trusted_information_retrieval() {
    env_logger::init();

    let (runtime, entry_handle) = oak_tests::run_single_module_default(MODULE_CONFIG_NAME)
        .expect("Unable to configure runtime with test wasm!");

    assert_matches!(
        send_config(&runtime, entry_handle, CONFIG_FILE.as_bytes().to_vec()),
        Ok(_)
    );

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = TrustedInformationRetrievalClient::with_interceptor(channel, interceptor);

    // Test nearest point of interest
    assert_matches!(submit_sample(&mut client, 4.0, -10.0).await, Err(_));
}
