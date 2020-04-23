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

const METRICS_PORT: u16 = 9876;

mod common {
    use oak_runtime::runtime::RuntimeProxy;

    use hyper::{Client, Uri};
    use log::info;
    use maplit::hashmap;
    use oak_abi::OakStatus;
    use oak_runtime::config;
    use wat::parse_str;

    pub fn start_runtime() -> Result<(RuntimeProxy, oak_abi::Handle), OakStatus> {
        let wat = r#"
        (module
            (type (;0;) (func (param i64)))
            (func $oak_main (type 0))
            (memory (;0;) 18)
            (export "memory" (memory 0))
            (export "oak_main" (func $oak_main)))
        "#;
        let binary = parse_str(wat).expect("Could not parse wat module.");

        // Create a runtime with one node
        let cfg = oak_runtime::application_configuration(
            hashmap![
                "node".to_string() => binary,
            ],
            "lumberjack",
            "node",
            "oak_main",
        );

        info!("Starting the runtime with one node.");
        config::configure_and_run(
            cfg,
            oak_runtime::RuntimeConfiguration {
                metrics_port: Some(crate::METRICS_PORT),
                introspect_port: None,
            },
        )
    }

    pub async fn read_metrics() -> Result<String, hyper::error::Error> {
        info!("Reading the metrics.");
        let client = Client::new();

        let uri = format!("http://localhost:{}", &super::METRICS_PORT)
            .parse::<Uri>()
            .expect("Could not parse URI.");

        let res = client.get(uri).await?;
        info!("status: {}", res.status());

        let buf = hyper::body::to_bytes(res).await?;
        Ok(std::str::from_utf8(&buf[..]).unwrap().to_string())
    }
}

fn get_int_metric_value(all_metrics: &str, metric_name: &str) -> Option<i64> {
    let pattern = format!(r"(.*)(\b{} \b)([0-9]+)(.*)", metric_name);
    let re = regex::Regex::new(&pattern).unwrap();
    re.captures(&all_metrics)
        .map(|c| c[3].parse::<i64>().unwrap())
}

#[test]
fn test_metrics_gives_the_correct_number_of_nodes() {
    env_logger::init();

    // Start the Runtime, including a metrics server.
    let (runtime, _initial_handle) = common::start_runtime().expect("Starting the Runtime failed!");

    let mut rt = tokio::runtime::Runtime::new().expect("Couldn't create Tokio runtime");
    let res = rt
        .block_on(common::read_metrics())
        .expect("Reading the metrics failed.");

    let value = get_int_metric_value(&res, "runtime_nodes_count");
    assert_eq!(value, Some(2));

    runtime.stop_runtime();
}
