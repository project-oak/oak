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

//! Weather Service example for Project Oak.

pub mod proto {
    pub mod oak {
        pub mod examples {
            pub mod weather_service {
                include!(concat!(env!("OUT_DIR"), "/oak.examples.weather_service.rs"));
            }
        }
    }
}

use crate::proto::oak::examples::weather_service::{
    GetCityWeatherRequest, GetCityWeatherResponse, Weather,
};
use prost::Message;

fn read_request() -> Result<Vec<u8>, ()> {
    Ok(vec![])
}

fn write_response(_response: &[u8]) -> Result<(), ()> {
    Ok(())
}

fn storage_get_item(_key: &str) -> Result<Vec<u8>, ()> {
    Ok(vec![])
}

#[no_mangle]
pub extern "C" fn main() {
    let request = read_request().expect("Couldn't read request");
    let decoded_request = GetCityWeatherRequest::decode(&mut std::io::Cursor::new(request))
        .expect("Couldn't decode request");

    let database_entry = storage_get_item(&decoded_request.city.to_uppercase())
        .expect("Couldn't get requested database entry");
    let decoded_database_entry = Weather::decode(&mut std::io::Cursor::new(database_entry))
        .expect("Couldn't decode request");
    let temperature = decoded_database_entry.temperature;

    let response = GetCityWeatherResponse {
        weather: Some(Weather {
            temperature: temperature,
        }),
    };
    let mut encoded_response = vec![];
    response
        .encode(&mut encoded_response)
        .expect("Couldn't encode response");
    write_response(&encoded_response).expect("Couldn't write response");
}
