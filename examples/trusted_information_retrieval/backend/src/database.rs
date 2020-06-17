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

use crate::proto::DatabaseEntry;
use anyhow::Context;
use log::debug;
use quick_xml::de::from_str;
use reqwest::Url;
use serde::Deserialize;

/// Database structure represents internal XML fields from the following database:
/// https://tfl.gov.uk/tfl/syndication/feeds/cycle-hire/livecyclehireupdates.xml
#[derive(Debug, Deserialize, PartialEq)]
pub struct Database {
    #[serde(rename = "lastUpdate", default)]
    last_update: String,
    version: String,
    #[serde(rename = "station", default)]
    stations: Vec<Station>,
}

#[derive(Clone, Debug, Deserialize, PartialEq)]
pub struct Station {
    id: u32,
    name: String,
    #[serde(rename = "terminalName", default)]
    terminal_name: String,
    #[serde(rename = "lat", default)]
    latitude_degrees: f32,
    #[serde(rename = "long", default)]
    longitude_degrees: f32,
    installed: bool,
    locked: bool,
    #[serde(rename = "installDate", default)]
    install_date: String,
    #[serde(rename = "removalDate", default)]
    removal_date: String,
    temporary: bool,
    #[serde(rename = "nbBikes", default)]
    number_of_bikes: u32,
    #[serde(rename = "nbEmptyDocks", default)]
    number_of_empty_docks: u32,
    #[serde(rename = "nbDocks", default)]
    number_of_docks: u32,
}

impl From<Station> for DatabaseEntry {
    fn from(station: Station) -> Self {
        Self {
            id: station.id,
            name: station.name.to_string(),
            terminal_name: station.terminal_name.to_string(),
            latitude_degrees: station.latitude_degrees,
            longitude_degrees: station.longitude_degrees,
            installed: station.installed,
            locked: station.locked,
            install_date: station.install_date.to_string(),
            removal_date: station.removal_date.to_string(),
            temporary: station.temporary,
            number_of_bikes: station.number_of_bikes,
            number_of_empty_docks: station.number_of_empty_docks,
            number_of_docks: station.number_of_docks,
        }
    }
}

/// Download an XML database from `url`.
pub async fn load_database(url: Url) -> anyhow::Result<Vec<DatabaseEntry>> {
    debug!("Loading database from {}", url);
    let response = reqwest::get(url)
        .await
        .context("Couldn't download database")?;
    let xml_database = response
        .text()
        .await
        .context("Couldn't retreive XML data from HTTP response")?;
    parse_database(&xml_database)
}

/// Parse an XML database into a vector of [`DatabaseEntry`].
pub fn parse_database(xml_database: &str) -> anyhow::Result<Vec<DatabaseEntry>> {
    let database: Database = from_str(xml_database).context("Couldn't parse XML data")?;

    // Transform [`Station`] deserialized by Serde to [`DatabaseEntry`] created by Protobuf.
    Ok(database
        .stations
        .iter()
        .cloned()
        .map(|station| station.into())
        .collect())
}
