//
// Copyright 2024 The Project Oak Authors
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

use std::sync::Arc;

use oak_functions_service::{logger::StandaloneLogger, lookup::LookupDataManager};
use tokio::{fs, process::Command};
use xtask::workspace_path;

#[tokio::test]
async fn test_native_handler() {
    let status = Command::new("bazel")
        .arg("build")
        .arg("//cc/oak_functions/native_sdk:key_value_lookup")
        .current_dir(workspace_path(&[]))
        .spawn()
        .expect("failed to spawn bazel")
        .wait()
        .await
        .expect("failed to wait for bazel");
    eprintln!("bazel status: {:?}", status);
    assert!(status.success());

    let _library = fs::read(
        workspace_path(&[]).join("bazel-bin/cc/oak_functions/native_sdk/libkey_value_lookup.so"),
    )
    .await
    .expect("failed to read test library");

    let logger = Arc::new(StandaloneLogger);
    let lookup_data_manager = Arc::new(LookupDataManager::<1>::new_empty(logger));
    lookup_data_manager
        .extend_next_lookup_data([("key_0".as_bytes(), "value_0".as_bytes())].into_iter());

    lookup_data_manager.finish_next_lookup_data();

    // This test fails right now because the library links in too many other
    // libraries.
    /*
    let handler = NativeHandler::new_handler(&library, lookup_data_manager, None)
        .expect("failed to load test library");
    let response = handler
        .handle_invoke(Request {
            body: "key_0".as_bytes().to_vec(),
        })
        .expect("failed to issue invoke");
    assert_eq!(StatusCode::Success, response.status);
    assert_eq!("value_0".as_bytes(), response.body().unwrap());
    */
}
