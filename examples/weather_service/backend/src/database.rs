//
// Copyright 2021 The Project Oak Authors
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

use crate::proto;
use anyhow::Context;
use serde::Deserialize;
use std::io::prelude::*;

#[derive(Clone, Debug, Default)]
pub struct Database {
    entries: Vec<DatabaseEntry>,
}

/// Database entry that contains weather information about a particular city.
#[derive(Clone, Debug, Deserialize)]
struct DatabaseEntry {
    city: City,
    time: u64,
    #[serde(rename = "main")]
    temperature: Temperature,
    wind: Wind,
    clouds: Clouds,
    weather: Vec<Weather>,
}

#[derive(Clone, Debug, Deserialize)]
struct City {
    id: u32,
    name: String,
    /// Uppercase name value used as a database entry key.
    #[serde(rename = "findname")]
    uppercase_name: String,
    country: String,
    #[serde(rename = "coord")]
    coordinates: Coordinates,
    zoom: u32,
}

#[derive(Clone, Debug, Deserialize)]
struct Coordinates {
    #[serde(rename = "lon")]
    longitude: f32,
    #[serde(rename = "lat")]
    latitude: f32,
}

#[derive(Clone, Debug, Deserialize)]
struct Temperature {
    #[serde(rename = "temp")]
    temperature: f32,
    pressure: f32,
    #[serde(rename = "temp_min")]
    temperature_min: f32,
    #[serde(rename = "temp_max")]
    temperature_max: f32,
    humidity: f32,
}

#[derive(Clone, Debug, Deserialize)]
struct Wind {
    speed: f32,
    #[serde(rename = "deg")]
    direction_degrees: f32,
}

#[derive(Clone, Debug, Deserialize)]
struct Clouds {
    all: u32,
}

#[derive(Clone, Debug, Deserialize)]
struct Weather {
    id: u32,
    main: String,
    description: String,
    icon: String,
}

/// Decode data from a GZIP encoded `data`.
/// https://tools.ietf.org/html/rfc1952
fn decode_gzip(data: &[u8]) -> anyhow::Result<String> {
    let mut decoder = flate2::read::GzDecoder::new(&data[..]);
    let mut decoded_data = String::new();
    decoder
        .read_to_string(&mut decoded_data)
        .context("Couldn't decode GZIP encoded data")?;
    Ok(decoded_data)
}

/// Parse a GZIP encoded JSON database into a [`Vec<Entry>`].
pub fn parse_database(database: &[u8]) -> anyhow::Result<proto::Database> {
    let database_string = decode_gzip(database)?;
    let parsed_database: Database = database_string
        .lines()
        .try_fold(
            Database::default(),
            |mut parsed_database, entry| match serde_json::from_str(entry) {
                Ok(parsed_entry) => {
                    parsed_database.entries.push(parsed_entry);
                    Ok(parsed_database)
                }
                Err(error) => Err(format!(
                    "Couldn't parse JSON database entry: {:?}: {:?}",
                    entry, error
                )),
            },
        )
        .map_err(|error| {
            anyhow::Error::msg(format!("Couldn't parse JSON database: {:?}", error))
        })?;

    Ok(parsed_database.into())
}

impl From<Database> for proto::Database {
    fn from(source: Database) -> Self {
        proto::Database {
            entries: source
                .entries
                .iter()
                .map(|entry| entry.clone().into())
                .collect(),
        }
    }
}

impl From<DatabaseEntry> for proto::DatabaseEntry {
    fn from(source: DatabaseEntry) -> Self {
        proto::DatabaseEntry {
            city: Some(source.city.into()),
            time: source.time,
            temperature: Some(source.temperature.into()),
            wind: Some(source.wind.into()),
            clouds: Some(source.clouds.into()),
            weather: source
                .weather
                .iter()
                .map(|weather| weather.clone().into())
                .collect(),
        }
    }
}

impl From<City> for proto::City {
    fn from(source: City) -> Self {
        proto::City {
            id: source.id,
            name: source.name,
            uppercase_name: source.uppercase_name,
            country: source.country,
            coordinates: Some(source.coordinates.into()),
            zoom: source.zoom,
        }
    }
}

impl From<Coordinates> for proto::Coordinates {
    fn from(source: Coordinates) -> Self {
        proto::Coordinates {
            longitude: source.longitude,
            latitude: source.latitude,
        }
    }
}

impl From<Temperature> for proto::Temperature {
    fn from(source: Temperature) -> Self {
        proto::Temperature {
            temperature: source.temperature,
            pressure: source.pressure,
            temperature_min: source.temperature_min,
            temperature_max: source.temperature_max,
            humidity: source.humidity,
        }
    }
}

impl From<Wind> for proto::Wind {
    fn from(source: Wind) -> Self {
        proto::Wind {
            speed: source.speed,
            direction_degrees: source.speed,
        }
    }
}

impl From<Clouds> for proto::Clouds {
    fn from(source: Clouds) -> Self {
        proto::Clouds { all: source.all }
    }
}

impl From<Weather> for proto::Weather {
    fn from(source: Weather) -> Self {
        proto::Weather {
            id: source.id,
            main: source.main,
            description: source.description,
            icon: source.icon,
        }
    }
}
