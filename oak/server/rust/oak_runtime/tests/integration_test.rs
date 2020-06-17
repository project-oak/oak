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

use oak_runtime::time::{RoughtimeClient, DEFAULT_MAX_RADIUS_MICROSECONDS};
use std::{sync::Once, time::SystemTime};

static LOG_INIT_ONCE: Once = Once::new();

const METRICS_PORT: u16 = 9876;

fn init_logging() {
    LOG_INIT_ONCE.call_once(|| {
        // Logger panics if it is initalized more than once.
        env_logger::init();
    });
}

mod common {
    use hyper::{Client, Uri};
    use log::info;
    use maplit::hashmap;
    use oak_abi::{
        proto::oak::application::{
            node_configuration::ConfigType, ApplicationConfiguration, NodeConfiguration,
            WebAssemblyConfiguration,
        },
        OakStatus,
    };
    use oak_runtime::{config, GrpcConfiguration, Runtime};
    use std::sync::Arc;
    use wat::parse_str;

    pub fn start_runtime() -> Result<Arc<Runtime>, OakStatus> {
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
        let application_configuration = ApplicationConfiguration {
            wasm_modules: hashmap! {
                "module".to_string() => binary,
            },
            initial_node_configuration: Some(NodeConfiguration {
                name: "test".to_string(),
                config_type: Some(ConfigType::WasmConfig(WebAssemblyConfiguration {
                    wasm_module_name: "module".to_string(),
                    wasm_entrypoint_name: "oak_main".to_string(),
                })),
            }),
        };

        info!("Starting the runtime with one node.");
        config::configure_and_run(oak_runtime::RuntimeConfiguration {
            metrics_port: Some(crate::METRICS_PORT),
            introspect_port: None,
            grpc_config: GrpcConfiguration::default(),
            app_config: application_configuration,
            config_map: None,
        })
    }

    pub async fn read_metrics() -> Result<String, hyper::error::Error> {
        info!("Reading the metrics.");
        let client = Client::new();

        let uri = format!("http://localhost:{}/metrics", &super::METRICS_PORT)
            .parse::<Uri>()
            .expect("Could not parse URI.");

        let res = client.get(uri).await?;
        info!("status: {}", res.status());

        let buf = hyper::body::to_bytes(res).await?;
        Ok(std::str::from_utf8(buf.as_ref()).unwrap().to_string())
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
    init_logging();

    // Start the Runtime, including a metrics server.
    let runtime = common::start_runtime().expect("Starting the Runtime failed!");

    let mut rt = tokio::runtime::Runtime::new().expect("Couldn't create Tokio runtime");
    let res = rt
        .block_on(common::read_metrics())
        .expect("Reading the metrics failed.");

    let value = get_int_metric_value(&res, "runtime_nodes_total");
    assert_eq!(value, Some(2), "{}", &res);

    let value = get_int_metric_value(&res, "runtime_health_check");
    assert_eq!(value, Some(1), "{}", &res);

    runtime.stop();
}

#[test]
#[ignore]
/// Gets Roughtime from the live default servers with the default settings.
///
/// This requires an internet connection, at least 3 of the default servers to be operational and
/// accessible, and that the test host machine's system clock is roughly accurate.
fn test_get_roughtime_live() {
    init_logging();
    let client = RoughtimeClient::default();
    let roughtime: u128 = client.get_roughtime().unwrap().into();
    let current = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_micros();

    assert!(
        roughtime.saturating_sub(DEFAULT_MAX_RADIUS_MICROSECONDS.into()) <= current
            && roughtime.saturating_add(DEFAULT_MAX_RADIUS_MICROSECONDS.into()) >= current
    );
}
