//
// Copyright 2025 The Project Oak Authors
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

use oak_proxy_lib::config::{ClientConfig, ServerConfig};

#[test]
fn read_config_test() {
    let client_config_str = std::fs::read_to_string("oak_proxy/testdata/client.toml")
        .expect("could not read client config");
    let server_config_str = std::fs::read_to_string("oak_proxy/testdata/server.toml")
        .expect("could not read server config");

    let client_config: Result<ClientConfig, _> = toml::from_str(&client_config_str);
    let server_config: Result<ServerConfig, _> = toml::from_str(&server_config_str);

    assert!(client_config.is_ok());
    assert!(server_config.is_ok());
}
