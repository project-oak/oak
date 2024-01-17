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

use std::sync::Once;

use oak_containers_launcher::Args;
use oak_crypto::encryptor::ClientEncryptor;
use once_cell::sync::Lazy;

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

static INIT_LOGGING: Once = Once::new();

fn init_logging() {
    INIT_LOGGING.call_once(|| {
        env_logger::init();
    });
}

static INIT_DEPENDENCIES: Lazy<anyhow::Result<()>> = Lazy::new(|| {
    // This takes a long time, but we want to make sure everything it up to date.
    // TODO(#4195): Stop dependencies from always being rebuilt.
    duct::cmd!("just", "all_oak_containers_binaries",)
        .dir(env!("WORKSPACE_ROOT"))
        .run()?;
    Ok(())
});

fn init_dependencies() {
    INIT_DEPENDENCIES
        .as_ref()
        .expect("couldn't build dependencies");
}

macro_rules! hello_world_tests {
    ($($name:ident: $container_bundle:expr,)*) => {
    $(
        #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
        async fn $name() {
            init_logging();

            if xtask::testing::skip_test() {
                log::info!("skipping test");
                return;
            }

            init_dependencies();

            let app_args = Args {
                container_bundle: $container_bundle.into(),
                ..Args::default_for_test()
            };
            let mut untrusted_app =
                oak_containers_hello_world_untrusted_app::UntrustedApp::create(app_args)
                    .await
                    .expect("could not create untrusted app");

            let get_endorsed_evidence_result = untrusted_app.get_endorsed_evidence().await;
            assert!(get_endorsed_evidence_result.is_ok());
            let endorsed_evidence = get_endorsed_evidence_result.unwrap();
            #[allow(deprecated)]
            let encryption_public_key = endorsed_evidence
                .attestation_evidence
                .expect("no attestation evidence provided")
                .encryption_public_key;

            let mut client_encryptor =
                ClientEncryptor::create(&encryption_public_key).expect("couldn't create client encryptor");
            let encrypted_request = client_encryptor
                .encrypt("fancy test".as_bytes(), EMPTY_ASSOCIATED_DATA)
                .expect("couldn't encrypt request");

            let encrypted_response = untrusted_app
                .hello(encrypted_request)
                .await
                .expect("couldn't get greeting");

            let (response, _) = client_encryptor
                .decrypt(&encrypted_response)
                .expect("couldn't decrypt response");
            let greeting = String::from_utf8(response).expect("couldn't parse response");

            untrusted_app.kill().await;

            log::info!("Greeting: {}", greeting);
            assert_eq!(greeting, "Hello from the trusted side, fancy test! Btw, the Trusted App has a config with a length of 0 bytes.");
        }
    )*
    }
}

hello_world_tests! {
    hello_world: Args::default_for_test().container_bundle,
    cc_hello_world: format!(
        "{}bazel-bin/cc/oak_containers_hello_world_trusted_app/bundle.tar",
        env!("WORKSPACE_ROOT")),
}
