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
use bencher::stats::Stats;
use oak_functions_abi::Request;
use oak_functions_client::Client;
use std::time::Instant;

// From https://pantheon.corp.google.com/api-gateway/gateway/weather-lookup-grpc/location/europe-west2?project=oak-ci.
const URL: &str = "https://weather-lookup-grpc-8tk01hn7.nw.gateway.dev";
// Test request coordinates are defined in `oak_functions/lookup_data_generator/src/data.rs`.
const REQUEST: &[u8] = br#"{"lat":0,"lng":0}"#;
const TOTAL_REQUESTS: usize = 50;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut client = Client::new(URL).await.context("Could not create client")?;

    let mut latencies_millis = Vec::<f64>::with_capacity(TOTAL_REQUESTS);

    for i in 0..TOTAL_REQUESTS {
        let start = Instant::now();
        let response = client
            .invoke(Request {
                body: REQUEST.to_vec(),
            })
            .await
            .context("Could not invoke Oak Functions instance")?;
        let elapsed_millis = start.elapsed().as_millis();
        latencies_millis.push(elapsed_millis as f64);
        println!(
            "#{:03}/{:03}: {:4?}ms: response: {:?}",
            i,
            TOTAL_REQUESTS,
            elapsed_millis,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    println!("-------- total --------");
    println!("mean: {:4.0}ms", &latencies_millis.mean());
    println!("min: {:4.0}ms", &latencies_millis.min());
    println!("max: {:4.0}ms", &latencies_millis.max());
    // See https://en.wikipedia.org/wiki/Median_absolute_deviation.
    println!(
        "median absolute deviation: {:4.0}ms",
        &latencies_millis.median_abs_dev()
    );

    Ok(())
}
