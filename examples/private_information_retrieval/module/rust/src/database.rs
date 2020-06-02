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

use crate::proto::{Location, PointOfInterest};
use log::{debug, error};
use oak::OakError;
use oak_abi::proto::oak::application::ConfigMap;
use quick_xml::de::from_str;
use serde::Deserialize;

/// Database structure represents internal XML fields from the following database:
/// https://tfl.gov.uk/tfl/syndication/feeds/cycle-hire/livecyclehireupdates.xml
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
            .map_err(|error| {
                error!("Couldn't convert vector to string: {:?}", error);
                OakError::OakStatus(oak_abi::OakStatus::ErrInvalidArgs)
            })?
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
        .filter(|station| station.installed && !station.locked && station.removal_date.is_empty())
        .map(|station| PointOfInterest {
            name: station.name.to_string(),
            location: Some(Location {
                latitude: station.latitude_degrees,
                longitude: station.longitude_degrees,
            }),
        })
        .collect();
    Ok(points_of_interest)
}
