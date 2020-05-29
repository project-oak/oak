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
//! This shows how an Oak Node can aggregate data samples and report aggregated values if there are
//! enough samples to hide individual contributors (enforces k-anonymity).
//!
//! Clients invoke the module by providing data samples that contain a bucket ID
//! and a Sparse Vector - a dictionary with integer keys.

use crate::proto::{Location, PointOfInterest};
use log::{debug, error};
use oak::OakError;
use oak_abi::proto::oak::application::ConfigMap;
use quick_xml::de::from_str;
use serde::Deserialize;

#[derive(Debug, Deserialize, PartialEq)]
struct Database {
    #[serde(rename = "lastUpdate", default)]
    last_update: String,
    version: String,
    #[serde(rename = "station", default)]
    stations: Vec<Station>,
}

#[derive(Debug, Deserialize, PartialEq)]
struct Station {
    id: u32,
    name: String,
    #[serde(rename = "terminalName", default)]
    terminal_name: String,
    lat: f32,
    long: f32,
    installed: bool,
    locked: bool,
    #[serde(rename = "installDate", default)]
    install_date: String,
    #[serde(rename = "removalDate", default)]
    removal_date: String,
    temporary: bool,
    #[serde(rename = "nbBikes", default)]
    nb_bikes: u32,
    #[serde(rename = "nbEmptyDocks", default)]
    nb_empty_docks: u32,
    #[serde(rename = "nbDocks", default)]
    nb_docks: u32,
}

/// Load an XML database from [`oak::ReadHandle`] and parse it.
pub fn load_database(in_channel: oak::ReadHandle) -> Result<Vec<PointOfInterest>, OakError> {
    debug!("Loading database");
    let receiver = oak::io::Receiver::new(in_channel);
    let config_map: ConfigMap = receiver.receive()?;
    match config_map.items.get("database") {
        Some(xml_database) => {
            let points_of_interest = parse_database(xml_database).map_err(|error| {
                error!("Couldn't parse database: {:?}", error);
                OakError::OakStatus(oak_abi::OakStatus::ErrInvalidArgs)
            })?;
            debug!("Database loaded - size: {:?}", points_of_interest.len());
            Ok(points_of_interest)
        }
        None => {
            error!("`database` configuration argument is not specified");
            Err(OakError::OakStatus(oak_abi::OakStatus::ErrInvalidArgs))
        }
    }
}

/// Parse an XML database into a vector of [`PointOfInterest`].
pub fn parse_database(xml_database: &[u8]) -> Result<Vec<PointOfInterest>, OakError> {
    let database: Database = from_str(
        String::from_utf8(xml_database.to_vec())
            .expect("Couldn't convert vector to string")
            .as_ref(),
    )
    .map_err(|error| {
        error!("Couldn't parse XML data: {:?}", error);
        OakError::OakStatus(oak_abi::OakStatus::ErrInvalidArgs)
    })?;

    let points_of_interest = database
        .stations
        .iter()
        // Filter out closed stations, and stations with no bikes.
        .filter(|station| station.installed && !station.locked && station.removal_date == "")
        .map(|station| PointOfInterest {
            name: station.name.to_string(),
            location: Some(Location {
                latitude: station.lat,
                longitude: station.long,
            }),
        })
        .collect();
    Ok(points_of_interest)
}
