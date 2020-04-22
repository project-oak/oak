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

use std::thread::{park, spawn};

mod common {
    use oak_runtime::runtime::{Handle, Runtime};

    use hyper::{Client, Uri};
    use log::info;
    use maplit::hashmap;
    use oak_abi::OakStatus;
    use oak_runtime::{config, metrics};
    use std::sync::Arc;
    use wat::parse_str;

    const PORT: u16 = 9876;

    pub fn start_runtime() -> Result<(Arc<Runtime>, Handle), OakStatus> {
        let wat = r#"
        (module
            (type (;0;) (func (param i64) (result i32)))
            (func $oak_main (type 0)
              i32.const 42)
            (memory (;0;) 18)
            (export "memory" (memory 0))
            (export "oak_main" (func $oak_main)))
        "#;
        let binary = parse_str(wat).unwrap();

        // Create a runtime with one node
        let cfg = oak_runtime::application_configuration(
            hashmap![
                "node".to_string() => binary,
            ],
            "lumberjack",
            "node",
            "main",
        );

        info!("Starting the runtime with one nodes.");
        config::configure_and_run(cfg)
    }

    pub fn start_metrics_server() {
        info!("Starting the metrics server");

        let mut tokio_runtime =
            tokio::runtime::Runtime::new().expect("Couldn't create Tokio runtime");
        let result = tokio_runtime.block_on(metrics::serve_metrics(PORT));

        info!("Exiting metrics server node thread {:?}", result);
    }

    pub async fn read_metrics() -> Result<String, hyper::error::Error> {
        info!("Reading the metrics.");
        let client = Client::new();

        let uri = format!("http://localhost:{}", &PORT)
            .parse::<Uri>()
            .unwrap();
        match client.get(uri).await {
            Err(e) => Err(e),
            Ok(res) => {
                info!("status: {}", res.status());

                // Concatenate the body stream into a single buffer...
                match hyper::body::to_bytes(res).await {
                    Err(e) => Err(e),
                    Ok(buf) => Ok(format!("{:?}", buf)),
                }
            }
        }
    }
}

#[test]
fn test_metrics_gives_the_correct_number_of_nodes() {
    simple_logger::init().unwrap();

    // Alternatively, one could start the runtime without spawning a new thread, but this seems to
    // be a more generic way of starting the runtime.
    let rt_handle = spawn(move || {
        let _res = common::start_runtime();
    });

    // start metrics server in a new thread
    let metrics_handle = spawn(move || {
        common::start_metrics_server();

        // Keep the server up until the test is complete.
        park();
    });

    let mut rt = tokio::runtime::Runtime::new().unwrap();
    let res = rt.block_on(common::read_metrics()).unwrap();
    assert_eq!(res, "b\"# HELP nodes_count Number of nodes in the runtime.\\n# TYPE nodes_count gauge\\nnodes_count 1\\n\"");

    metrics_handle.thread().unpark();
    let _ = rt_handle.join();
}
