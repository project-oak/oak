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

use std::{env, sync::Once};

use oak_client::verifier::{AttestationVerifier, InsecureAttestationVerifier};
use oak_containers_launcher::{proto::oak::key_provisioning::v1::GetGroupKeysRequest, Args};
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
    if env::var("OAK_CONTAINERS_BINARIES_ALREADY_BUILT").unwrap_or_default().is_empty() {
        log::info!("Rebuilding all_oak_containers_binaries.");
        log::info!(
            "To prevent this, set the OAK_CONTAINERS_BINARIES_ALREADY_BUILT environment variable."
        );
        duct::cmd!("just", "all_oak_containers_binaries",).dir(env!("WORKSPACE_ROOT")).run()?;
    }

    Ok(())
});

fn init_dependencies() {
    INIT_DEPENDENCIES.as_ref().expect("couldn't build dependencies");
}

async fn run_hello_world_test(container_bundle: std::path::PathBuf) {
    init_logging();

    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    init_dependencies();

    let app_args = Args { container_bundle, ..Args::default_for_root(env!("WORKSPACE_ROOT")) };
    let mut untrusted_app =
        oak_containers_hello_world_untrusted_app::UntrustedApp::create(app_args)
            .await
            .expect("could not create untrusted app");

    let get_endorsed_evidence_result = untrusted_app.get_endorsed_evidence().await;
    assert!(get_endorsed_evidence_result.is_ok());
    let endorsed_evidence = get_endorsed_evidence_result.unwrap();

    // Use enclave's own endorsed evidence to verify that Key Provisioning works
    // and returns an encrypted key.
    let get_group_keys_request = GetGroupKeysRequest {
        evidence: endorsed_evidence.evidence.clone(),
        endorsements: endorsed_evidence.endorsements.clone(),
    };
    untrusted_app
        .get_group_keys(get_group_keys_request)
        .await
        .expect("couldn't get group keys for key provisioning");

    let evidence = endorsed_evidence.evidence.expect("no evidence provided");
    let endorsements = endorsed_evidence.endorsements.expect("no endorsements provided");
    let attestation_verifier = InsecureAttestationVerifier {};
    let attestation_results = attestation_verifier
        .verify(&evidence, &endorsements)
        .expect("couldn't verify endorsed evidence");

    let mut client_encryptor = ClientEncryptor::create(&attestation_results.encryption_public_key)
        .expect("couldn't create client encryptor");
    let encrypted_request = client_encryptor
        .encrypt("fancy test".as_bytes(), EMPTY_ASSOCIATED_DATA)
        .expect("couldn't encrypt request");

    let encrypted_response =
        untrusted_app.hello(encrypted_request).await.expect("couldn't get greeting");

    let (response, _) =
        client_encryptor.decrypt(&encrypted_response).expect("couldn't decrypt response");
    let greeting = String::from_utf8(response).expect("couldn't parse response");

    untrusted_app.kill().await;

    log::info!("Greeting: {}", greeting);
    assert_eq!(
        greeting,
        "Hello from the trusted side, fancy test! Btw, the Trusted App has a config with a length of 0 bytes."
    );
}

async fn hello_world() {
    run_hello_world_test(Args::default_for_root(env!("WORKSPACE_ROOT")).container_bundle).await;
}

async fn cc_hello_world() {
    run_hello_world_test(
        format!(
            "{}bazel-bin/cc/containers/hello_world_trusted_app/bundle.tar",
            env!("WORKSPACE_ROOT")
        )
        .into(),
    )
    .await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn all_hello_world() {
    // Combine both test cases into one test to avoid running them in parallel.
    // Nextest runs each test case in a separate process, which means that even
    // though they appear to be sharing synchronized state, that state is not
    // synchronized, and therefore they both end up rebuilding the dependencies
    // through the Lazy cell above. See https://nexte.st/book/usage.html?highlight=process#limitations
    hello_world().await;
    cc_hello_world().await;
}
