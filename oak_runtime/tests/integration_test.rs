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
use std::time::SystemTime;

const METRICS_PORT: u16 = 9876;

fn init_logging() {
    let _ = env_logger::builder().is_test(true).try_init();
}

mod common {
    use hyper::{Client, Uri};
    use log::info;
    use maplit::hashmap;
    use oak_abi::proto::oak::application::{
        node_configuration::ConfigType, ApplicationConfiguration, ConfigMap, NodeConfiguration,
        WebAssemblyConfiguration,
    };
    use oak_io::OakError;
    use oak_runtime::{config, Runtime, SecureServerConfiguration, SignatureTable};
    use std::sync::Arc;
    use wat::parse_str;

    pub fn start_runtime() -> Result<Arc<Runtime>, OakError> {
        // Loop 100 000 times in the main function to make sure the Wasm node is alive for a while
        // before exiting. This is needed to avoid a race condition causing
        // `test_metrics_gives_the_correct_number_of_nodes` to sometimes fail. If the Wasm node has
        // finished execution before the metrics count is requested the reported node count will be
        // incorrect.
        //
        // TODO(#2026): Change to infinite loop once the runtime can interrupt the Wasm node's
        // execution.
        let wat = r#"
        (module
            (type (;0;) (func (param i64)))
            (func $oak_main (type 0)
                (local i64)             ;; Declare local variable.
                i64.const 100000
                local.set 1             ;; Set local variable to 100 000.
                (block                  ;; Outer block.
                    (loop               ;; Inner block for loop.
                        local.get 1     ;; Load local variable.
                        i64.const -1
                        i64.add         ;; Add -1.
                        local.tee 1     ;; Store local variable, but keep value for comaprison.
                        i64.eqz
                        br_if 1         ;; Jump back to outer block if local variable is 0.
                        br 0)))         ;; Jump back to start of loop inner block.
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
                config_type: Some(ConfigType::WasmConfig(WebAssemblyConfiguration {
                    wasm_module_name: "module".to_string(),
                    wasm_entrypoint_name: "oak_main".to_string(),
                })),
            }),
            module_signatures: vec![],
        };
        let permissions = oak_runtime::permissions::PermissionsConfiguration {
            allow_grpc_server_nodes: true,
            ..Default::default()
        };

        info!("Starting the runtime with one node.");
        config::configure_and_run(oak_runtime::RuntimeConfiguration {
            metrics_port: Some(crate::METRICS_PORT),
            introspect_port: None,
            kms_credentials: None,
            secure_server_configuration: SecureServerConfiguration::default(),
            app_config: application_configuration,
            permissions_config: permissions,
            sign_table: SignatureTable::default(),
            config_map: ConfigMap::default(),
        })
    }

    pub async fn read_metrics() -> Result<String, hyper::Error> {
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
    re.captures(all_metrics)
        .map(|c| c[3].parse::<i64>().unwrap())
}

#[test]
fn test_metrics_gives_the_correct_number_of_nodes() {
    init_logging();

    // Start the Runtime, including a metrics server.
    let runtime = common::start_runtime().expect("Starting the Runtime failed!");

    let rt = tokio::runtime::Runtime::new().expect("Couldn't create Tokio runtime");
    let res = rt
        .block_on(common::read_metrics())
        .expect("Reading the metrics failed.");

    let value = get_int_metric_value(&res, "runtime_nodes_total\\{node_type=\"implicit\"\\}");
    assert_eq!(value, Some(1), "{}", &res);
    let value = get_int_metric_value(&res, "runtime_nodes_total\\{node_type=\"wasm\"\\}");
    assert_eq!(value, Some(1), "{}", &res);

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
