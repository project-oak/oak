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

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.weather_service.rs"));
}
mod database;

use anyhow::Context;
use database::parse_database;
use log::{error, info};
use proto::Database;
use reqwest::Url;
use std::sync::Arc;
use structopt::StructOpt;
use tokio::sync::Mutex;

const SAMPLE_DATABASE_URL: &str = "http://bulk.openweathermap.org/sample/weather_14.json.gz";

#[derive(StructOpt, Clone)]
#[structopt(about = "Weather Service Backend")]
pub struct Opt {
    #[structopt(
        long,
        help = "Weather File Name (`weather_14.json.gz` or `weather_16.json.gz`)",
        default_value = "weather_14.json.gz"
    )]
    bulk_file_name: String,
    #[structopt(long, help = "Unique API key for OpenWeather", default_value = "")]
    api_key: String,
    #[structopt(
        long,
        help = "URL of the Oak application to send the database to",
        default_value = "http://localhost:8080"
    )]
    application_url: String,
}

/// Download a JSON database from `url`.
pub async fn load_database(url: Url) -> anyhow::Result<Database> {
    info!("Downloading database from {}", url);
    let response = reqwest::get(url)
        .await
        .context("Couldn't download database")?;
    let database = response
        .bytes()
        .await
        .context("Couldn't retrieve data from HTTP response")?;

    info!("Parsing database");
    parse_database(&database).context("Couldn't parse database")
}

/// Send `database` to the Oak application `url`.
pub async fn send_database(url: Url, database: Arc<Mutex<Database>>) -> anyhow::Result<()> {
    info!("Sending database to {}", url);
    let database_entries = database.lock().await;
    info!("Database: {:?}", database_entries);
    // let response = reqwest::Client::new()
    //     .post(url)
    //     .body(database_entries)
    //     .send()
    //     .await
    //     .context("Couldn't send HTTP POST request")?;
    Ok(())
}

/// Loop for requesting a new database version from `url`.
async fn update_database_loop(
    database_url: Url,
    application_url: Url,
    database: Arc<Mutex<Database>>,
) {
    loop {
        // Download weather data from OpenWeather.
        // http://bulk.openweathermap.org
        match load_database(database_url.clone()).await {
            Ok(updated_database_entries) => {
                let mut database_entries = database.lock().await;
                *database_entries = updated_database_entries;
            }
            Err(error) => error!("Error loading database: {:?}", error),
        }

        // Create a separate asynchronous task for sending the database to Oak.
        tokio::spawn(send_database(application_url.clone(), database.clone()));

        // Wait for a minute before updating the database.
        tokio::time::delay_for(tokio::time::Duration::from_secs(60)).await;
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    env_logger::init();
    let opt = Opt::from_args();

    let database_url = Url::parse(SAMPLE_DATABASE_URL).expect("Couldn't parse database URL");
    let application_url = Url::parse(&opt.application_url).expect("Couldn't parse application URL");

    // Create a mutex-protected database.
    let database = Arc::new(Mutex::new(Database::default()));

    update_database_loop(database_url, application_url, database.clone()).await;

    Ok(())
}
