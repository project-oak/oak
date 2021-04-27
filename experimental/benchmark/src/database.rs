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

use crate::proto::{Location, PointOfInterest, PointOfInterestMap};
use log::info;
use rand::{rngs::SmallRng, Rng, SeedableRng};
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, time::Instant};

/// Database structure represents internal XML fields from the following database:
/// https://tfl.gov.uk/tfl/syndication/feeds/cycle-hire/livecyclehireupdates.xml
#[derive(Debug, Default, Serialize, Deserialize, PartialEq)]
struct StationDatabase {
    #[serde(rename = "lastUpdate", default)]
    last_update: String,
    version: String,
    #[serde(rename = "station", default)]
    stations: Vec<Station>,
}

#[derive(Debug, Default, Serialize, Deserialize, PartialEq)]
struct Station {
    id: u32,
    name: String,
    #[serde(rename = "terminalName", default)]
    terminal_name: String,
    #[serde(rename = "lat", default)]
    latitude_degrees: f32,
    #[serde(rename = "long", default)]
    longitude_degrees: f32,
    #[serde(default)]
    installed: bool,
    #[serde(default)]
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

pub struct Database {
    pub points_of_interest: PointOfInterestMap,
}

impl Database {
    pub fn new(size: usize) -> Self {
        let mut rng = SmallRng::seed_from_u64(0);

        let mut entries = HashMap::new();
        for id in 0..size {
            let name: u16 = rng.gen();
            let latitude_degrees: f32 = rng.gen_range(-90.0..90.0);
            let longitude_degrees: f32 = rng.gen_range(-180.0..180.0);
            let entry = PointOfInterest {
                name: format!("{}", name),
                location: Some(Location {
                    latitude_degrees,
                    longitude_degrees,
                }),
            };
            entries.insert(format!("{}", id), entry);
        }
        Self {
            points_of_interest: PointOfInterestMap { entries },
        }
    }

    pub fn serialize(&self) -> String {
        let stations: Vec<Station> = self
            .points_of_interest
            .entries
            .iter()
            .map(|(key, value)| {
                let location = value.location.as_ref().expect("Empty location");
                Station {
                    id: key.parse().expect("Couldn't parse key"),
                    name: value.name.to_string(),
                    latitude_degrees: location.latitude_degrees,
                    longitude_degrees: location.longitude_degrees,
                    ..Default::default()
                }
            })
            .collect();
        let station_database = StationDatabase {
            last_update: "".to_string(),
            version: "0.1".to_string(),
            stations,
        };
        // We need to manually update the resulting string, because `quick_xml` doesn't serialize
        // vectors correctly:
        // https://github.com/tafia/quick-xml/issues/204
        let database = quick_xml::se::to_string(&station_database)
            .expect("Couldn't serialize database")
            .replace("<station>", "")
            .replace("</station>", "")
            .replace("<Station ", "<station ")
            .replace("<Station>", "<station>")
            .replace("</Station>", "</station>");

        // Measure database parsing time. It is necessary to compare XML parsing time difference
        // between Oak and native applications.
        let start = Instant::now();
        let parsed_database: StationDatabase =
            quick_xml::de::from_str(&database).expect("Couldn't deserialize database");
        let duration = start.elapsed();
        info!(
            "Database parsing time: {:?} for {} entries ({} bytes)",
            duration,
            parsed_database.stations.len(),
            database.as_bytes().len()
        );

        database
    }
}
