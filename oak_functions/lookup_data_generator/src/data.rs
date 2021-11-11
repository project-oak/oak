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

use anyhow::Context;
use bytes::BytesMut;
use location_utils::{
    cell_id_to_bytes, find_covering_cells, location_from_degrees, location_to_bytes, Angle,
    DEFAULT_CUTOFF_RADIUS_RADIANS, S2_DEFAULT_LEVEL,
};
use multimap::MultiMap;
use oak_functions_abi::proto::Entry;
use prost::Message;
use rand::Rng;
use serde::Serialize;

fn create_bytes<R: Rng>(rng: &mut R, size_bytes: usize) -> Vec<u8> {
    let mut buf = vec![0u8; size_bytes];
    rng.fill(buf.as_mut_slice());
    buf
}

fn create_random_entry<R: Rng>(
    rng: &mut R,
    key_size_bytes: usize,
    value_size_bytes: usize,
) -> Entry {
    Entry {
        key: create_bytes(rng, key_size_bytes),
        value: create_bytes(rng, value_size_bytes),
    }
}

/// Generates random lookup entries with the specified sizes for keys and values and serializes it
/// to bytes.
pub fn generate_and_serialize_random_entries<R: Rng>(
    rng: &mut R,
    key_size_bytes: usize,
    value_size_bytes: usize,
    entries: usize,
) -> anyhow::Result<BytesMut> {
    let mut buf = BytesMut::new();
    for _ in 0..entries {
        let entry = create_random_entry(rng, key_size_bytes, value_size_bytes);
        entry
            .encode_length_delimited(&mut buf)
            .context("could not encode entry")?;
    }
    Ok(buf)
}

#[derive(Serialize)]
struct WeatherValue {
    temperature_degrees_celsius: i32,
}

fn create_weather_entry<R: Rng>(rng: &mut R, lat: i32, lng: i32) -> Entry {
    let key = format!("{},{}", lat, lng);
    let value = serde_json::to_string(&create_weather_value(rng)).unwrap();
    Entry {
        key: key.as_bytes().to_vec(),
        value: value.as_bytes().to_vec(),
    }
}

fn create_weather_value<R: Rng>(rng: &mut R) -> WeatherValue {
    let dist = rand::distributions::Uniform::new(-30, 40);
    WeatherValue {
        temperature_degrees_celsius: rng.sample(dist),
    }
}

/// Generates a dense set of random weather lookup entries with one entry for each comibnation of
/// full degree of longitude and latitude.
pub fn generate_and_serialize_weather_entries<R: Rng>(rng: &mut R) -> anyhow::Result<BytesMut> {
    let mut buf = BytesMut::new();
    for lat in -90..=90 {
        for lng in -180..=180 {
            let entry = create_weather_entry(rng, lat, lng);
            entry
                .encode_length_delimited(&mut buf)
                .context("could not encode entry")?;
        }
    }
    Ok(buf)
}

/// Generates a sparse set of random weather lookup entries with a random location for each entry.
pub fn generate_and_serialize_sparse_weather_entries<R: Rng>(
    rng: &mut R,
    entries: usize,
) -> anyhow::Result<BytesMut> {
    let mut buf = BytesMut::new();
    let pi = std::f64::consts::PI;
    // We sample longitude in radians from [-pi, pi).
    let lng_dist = rand::distributions::Uniform::new(-pi, pi);
    // To avoid increased density towards the poles, we sample latitude in the range [-1, 1] and
    // convert to latitude using `acos`. See https://mathworld.wolfram.com/SpherePointPicking.html
    let lat_dist = rand::distributions::Uniform::new(-1.0_f64, 1.0);
    let mut cell_map = MultiMap::new();
    for i in 0..entries {
        // Fix the first point to ensure the default example can find at least one data point within
        // 40km.
        // The first point is used in:
        // - `oak_functions/load_test/src/main.rs`
        // - `oak_functions/client/android/com/google/oak/functions/android/client/res/values/
        //   strings.xml`
        // - `oak_functions/examples/key_value_lookup/example.toml`
        // - `oak_functions/examples/weather_lookup/README.md`
        // - `oak_functions/examples/weather_lookup/example.toml`
        // - `oak_functions/examples/weather_lookup/client/java/src/Main.java`
        // - `oak_functions/examples/weather_lookup/scripts/cloud_run_deploy`
        let latitude_degrees = if i == 0 {
            0.0_f64
        } else {
            rng.sample(lat_dist).acos().to_degrees()
        };
        let longitude_degrees = if i == 0 {
            0.0_f64
        } else {
            rng.sample(lng_dist).to_degrees()
        };

        let location = location_from_degrees(latitude_degrees, longitude_degrees);

        let key = location_to_bytes(&location);
        // Add cell-based lookup index entries.
        for cell in find_covering_cells(
            &location,
            &Angle::from(DEFAULT_CUTOFF_RADIUS_RADIANS),
            S2_DEFAULT_LEVEL,
        )
        .unwrap()
        .iter()
        {
            cell_map.insert(cell_id_to_bytes(cell), key.to_vec());
        }
        let value = serde_json::to_string(&create_weather_value(rng)).unwrap();
        let entry = Entry {
            key: key.to_vec(),
            value: value.as_bytes().to_vec(),
        };
        entry
            .encode_length_delimited(&mut buf)
            .context("could not encode entry")?;
    }
    // Add the cell-based index entries.
    for (key, values) in cell_map.iter_all() {
        let cell_entry = Entry {
            key: key.clone(),
            value: values.concat(),
        };
        cell_entry
            .encode_length_delimited(&mut buf)
            .context("could not encode cell index")?;
    }
    Ok(buf)
}
