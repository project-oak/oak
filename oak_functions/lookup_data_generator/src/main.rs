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
use oak_functions_abi::proto::Entry;
use prost::Message;
use rand::Rng;
use serde::Serialize;
use std::{fs::File, io::Write};
use structopt::StructOpt;

#[derive(StructOpt, Clone, Debug)]
#[structopt(about = "Oak Functions Lookup Data Generator")]
pub struct Opt {
    #[structopt(long)]
    out_file_path: String,
    #[structopt(subcommand)]
    cmd: Command,
}

#[derive(StructOpt, Clone, Debug)]
pub enum Command {
    #[structopt(about = "Generate random key value pairs")]
    Random {
        #[structopt(long, default_value = "20")]
        key_size_bytes: usize,
        #[structopt(long, default_value = "1000")]
        value_size_bytes: usize,
        #[structopt(long, default_value = "100")]
        entries: usize,
    },
    #[structopt(about = "Generate entries for the weather lookup example with random values")]
    Weather {},
    #[structopt(
        about = "Generate sparse entries plus an index for the weather lookup example with random values"
    )]
    WeatherSparse {
        #[structopt(long, default_value = "100000")]
        entries: usize,
    },
}

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

#[derive(Serialize)]
struct WeatherValue {
    temperature_degrees_celsius: i32,
}

fn create_weather_entry<R: Rng>(rng: &mut R, lat: i32, lon: i32) -> Entry {
    let key = format!("{},{}", lat, lon);
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

fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();
    let mut buf = BytesMut::new();
    let mut rng = rand::thread_rng();
    match opt.cmd {
        Command::Random {
            key_size_bytes,
            value_size_bytes,
            entries,
        } => {
            for _ in 0..entries {
                let entry = create_random_entry(&mut rng, key_size_bytes, value_size_bytes);
                entry
                    .encode_length_delimited(&mut buf)
                    .context("could not encode entry")?;
            }
        }
        Command::Weather {} => {
            for lat in -90..=90 {
                for lon in -180..=180 {
                    let entry = create_weather_entry(&mut rng, lat, lon);
                    entry
                        .encode_length_delimited(&mut buf)
                        .context("could not encode entry")?;
                }
            }
        }
        Command::WeatherSparse { entries } => {
            let lat_dist = rand::distributions::Uniform::new(-90_000, 90_000);
            let lon_dist = rand::distributions::Uniform::new(-180_000, 180_000);
            let mut keys = vec![];
            for _ in 0..entries {
                let latitude_millidegrees: i32 = rng.sample(lat_dist);
                let longitude_millidegrees: i32 = rng.sample(lon_dist);
                let key = [
                    latitude_millidegrees.to_be_bytes(),
                    longitude_millidegrees.to_be_bytes(),
                ]
                .concat();
                keys.push(key.clone());
                let value = serde_json::to_string(&create_weather_value(&mut rng)).unwrap();
                let entry = Entry {
                    key: key.clone(),
                    value: value.as_bytes().to_vec(),
                };
                entry
                    .encode_length_delimited(&mut buf)
                    .context("could not encode entry")?;
            }
            let index = Entry {
                key: "index".as_bytes().to_vec(),
                value: keys.concat(),
            };
            index
                .encode_length_delimited(&mut buf)
                .context("could not encode index")?;
        }
    }
    let mut file = File::create(opt.out_file_path).context("could not create out file")?;
    file.write_all(&buf).context("could not write to file")?;
    Ok(())
}
