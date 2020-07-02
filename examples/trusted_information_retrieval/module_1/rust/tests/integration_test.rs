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
use trusted_information_retrieval_client::proto::{
    database_proxy_client::DatabaseProxyClient, GetDatabaseEntryRequest, GetDatabaseEntryResponse,
};

const MODULE_WASM_FILE_NAME: &str = "database_proxy.wasm";
const MODULE_ENTRYPOINT_NAME: &str = "grpc_database_proxy_main";

const DATABASE_URL: &str = "https://localhost:8888";

async fn get_database_entry(
    client: &mut DatabaseProxyClient<tonic::transport::Channel>,
    key: &str,
    database_url: &str,
) -> Result<tonic::Response<GetDatabaseEntryResponse>, tonic::Status> {
    let request = GetDatabaseEntryRequest {
        key: key.to_string(),
        database_url: database_url.to_string(),
    };
    client.get_database_entry(request).await
}

#[tokio::test(core_threads = 2)]
async fn test_database_proxy_for_unavailable_database() {
    env_logger::init();

    let runtime = oak_tests::run_single_module(MODULE_WASM_FILE_NAME, MODULE_ENTRYPOINT_NAME)
        .expect("Unable to configure runtime with test wasm!");

    let (channel, interceptor) = oak_tests::channel_and_interceptor().await;
    let mut client = DatabaseProxyClient::with_interceptor(channel, interceptor);

    // Test database entry.
    assert_matches!(
        get_database_entry(&mut client, "0", DATABASE_URL).await,
        Err(_)
    );

    runtime.stop();
}
