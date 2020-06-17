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
use oak_abi::proto::oak::application::ConfigMap;

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    database_url: String,
}

pub fn get_database_url(config_map: ConfigMap) -> anyhow::Result<String> {
    let config_file = config_map
        .items
        .get("config")
        .context("`config` argument is not specified")?
        .to_vec();

    let config: Config =
        toml::from_str(&String::from_utf8(config_file).context("Couldn't convert to string")?)
            .context("Couldn't parse TOML config file")?;
    Ok(config.database_url)
}
