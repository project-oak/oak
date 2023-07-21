//
// Copyright 2023 The Project Oak Authors
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

//! Integration test that launches the trusted app and invokes it.

use oak_containers_launcher::Args;
use std::sync::Once;

static INIT: Once = Once::new();

fn init_logging() {
    INIT.call_once(|| {
        env_logger::init();
    });
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn hello_world() {
    init_logging();

    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    // This takes a long time, but we want to make sure everything it up to date.
    // TODO(#4195): Stop dependencies from always being rebuilt.
    build_dependencies().expect("couldn't build dependencies");

    let mut untrusted_app =
        oak_containers_hello_world_untrusted_app::UntrustedApp::create(Args::default_for_test())
            .await
            .expect("could not create untrusted app");
    let greeting = untrusted_app
        .hello("fancy test")
        .await
        .expect("couldn't get greeting");

    untrusted_app.kill().await;

    log::info!("Greeting: {}", greeting);
    assert_eq!(greeting, "Hello from the trusted side, fancy test! Btw, the Trusted App has a config with a length of 0 bytes.");
}

fn build_dependencies() -> anyhow::Result<()> {
    duct::cmd!("just", "all_oak_containers_binaries",)
        .dir(env!("WORKSPACE_ROOT"))
        .run()?;
    Ok(())
}
