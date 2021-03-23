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

//! Client for the Weather Service example.

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.weather_service.rs"));
}

use crate::proto::{GetCityWeatherRequest, GetCityWeatherResponse};
use anyhow::Context;
use log::info;
use prost::Message;
use reqwest::Url;
use structopt::StructOpt;

#[derive(StructOpt, Clone)]
#[structopt(about = "Weather Service Client")]
pub struct Opt {
    #[structopt(
        long,
        help = "URL of the Oak application to connect to",
        default_value = "https://localhost:8080/invoke"
    )]
    application_url: String,
    #[structopt(long, help = "City name to request weather information for")]
    city_name: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let application_url =
        Url::parse(&opt.application_url).context("Couldn't parse application URI")?;

    let request = GetCityWeatherRequest {
        city_name: opt.city_name,
    };
    let mut encoded_request = vec![];
    request
        .encode(&mut encoded_request)
        .expect("Couldn't encode response");

    let client = reqwest::Client::new();
    let response = client
        .post(application_url)
        .body(encoded_request)
        .send()
        .await
        .context("Couldn't request weather information")?
        .bytes()
        .await
        .context("Couldn't retrieve data from HTTP response")?;
    let decoded_response = GetCityWeatherResponse::decode(&mut std::io::Cursor::new(response))
        .expect("Couldn't decode response");
    info!("Weather: {:?}", decoded_response.entry);

    Ok(())
}
