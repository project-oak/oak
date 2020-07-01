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
use oak_abi::proto::oak::application::ConfigMap;
use trusted_information_retrieval_client::proto::{
    trusted_information_retrieval_client::TrustedInformationRetrievalClient,
    GetPointOfInterestRequest, GetPointOfInterestResponse,
};

const MODULE_WASM_FILE_NAME: &str = "trusted_information_retrieval.wasm";
const ENTRYPOINT_NAME: &str = "oak_main";

const CONFIG_FILE: &str = r#"
database_url = "https://localhost:8888"
"#;

async fn get_point_of_interest(
    client: &mut TrustedInformationRetrievalClient<tonic::transport::Channel>,
    id: &str,
) -> Result<tonic::Response<GetPointOfInterestResponse>, tonic::Status> {
    let request = GetPointOfInterestRequest { id: id.to_string() };
    client.get_point_of_interest(request).await
}

#[tokio::test(core_threads = 2)]
async fn test_trusted_information_retrieval_for_unavailable_database() {
    env_logger::init();

    // Send test database as a start-of-day config map.
    let config_map = ConfigMap {
        items: hashmap! {"config".to_string() => CONFIG_FILE.as_bytes().to_vec()},
    };
    let runtime = oak_tests::run_single_module_with_config(
        MODULE_WASM_FILE_NAME,
        ENTRYPOINT_NAME,
        config_map,
    )
    .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = TrustedInformationRetrievalClient::with_interceptor(channel, interceptor);

    // Test nearest point of interest.
    assert_matches!(get_point_of_interest(&mut client, "0").await, Err(_));

    runtime.stop();
}
