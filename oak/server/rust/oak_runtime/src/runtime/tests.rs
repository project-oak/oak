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

use super::*;
use std::sync::Once;

static LOG_INIT_ONCE: Once = Once::new();

pub fn init_logging() {
    LOG_INIT_ONCE.call_once(|| {
        // Logger panics if it is initalized more than once.
        simple_logger::init_by_env();
    });
}

type NodeBody = dyn Fn(RuntimeProxy) -> Result<(), OakStatus> + Send + Sync;

/// Runs the provided function as if it were the body of a [`Node`] implementation, which is
/// instantiated by the [`Runtime`] with the provided [`Label`].
fn run_node_body(node_label: &Label, node_body: Box<NodeBody>) {
    init_logging();
    let configuration = crate::runtime::Configuration {
        nodes: maplit::hashmap![
            "log".to_string() => crate::node::Configuration::LogNode,
        ],
        entry_module: "test_module".to_string(),
        entrypoint: "test_function".to_string(),
    };
    info!("Create runtime for test");
    let proxy = crate::RuntimeProxy::create_runtime(configuration);

    struct TestNode {
        node_body: Box<NodeBody>,
    };

    impl crate::node::Node for TestNode {
        fn run(self: Box<Self>, runtime: RuntimeProxy, _handle: oak_abi::Handle) {
            let _ = (self.node_body)(runtime);
        }
    }

    // Create a new Node.
    info!("Create test Node");
    let test_proxy = proxy.clone().runtime.proxy_for_new_node();
    let new_node_id = test_proxy.node_id;
    let new_node_name = format!("TestNode({})", new_node_id.0);
    proxy
        .runtime
        .node_configure_instance(new_node_id, "test_module.test_function", &node_label);

    let node_instance = TestNode { node_body };
    info!("Start test Node instance");
    let result = proxy.runtime.node_start_instance(
        &new_node_name,
        Box::new(node_instance),
        test_proxy,
        oak_abi::INVALID_HANDLE,
    );
    assert_eq!(Ok(()), result);
}

/// Returns a non-trivial label for testing.
fn test_label() -> Label {
    Label {
        secrecy_tags: vec![oak_abi::label::authorization_bearer_token_hmac_tag(&[
            1, 1, 1,
        ])],
        integrity_tags: vec![],
    }
}

/// Checks that a panic in the node body actually causes the test case to fail, and does not
/// accidentally get ignored.
#[test]
#[ignore]
#[should_panic]
fn panic_check() {
    let label = test_label();
    run_node_body(
        &label,
        Box::new(|_runtime| {
            panic!("testing that panic works");
        }),
    );
}

/// Create a test Node that creates a Channel with the same label and succeeds.
#[test]
fn create_channel_same_label_ok() {
    let label = test_label();
    let label_clone = label.clone();
    run_node_body(
        &label,
        Box::new(move |runtime| {
            // Attempt to perform an operation that requires the [`Runtime`] to have created an
            // appropriate [`NodeInfo`] instance.
            let result = runtime.channel_create(&label_clone);
            assert_eq!(true, result.is_ok());
            Ok(())
        }),
    );
}

/// Create a test Node that creates a Channel with a less secret label and fails.
///
/// If this succeeded, it would be a violation of information flow control, since the original
/// secret Node would be able to spawn "less secret / public" Channels and use their side effects as
/// a covert channel to exfiltrate secret data.
#[test]
fn create_channel_less_secret_label_err() {
    let initial_label = Label {
        secrecy_tags: vec![oak_abi::label::authorization_bearer_token_hmac_tag(&[
            1, 1, 1,
        ])],
        integrity_tags: vec![],
    };
    let less_secret_label = Label {
        secrecy_tags: vec![],
        integrity_tags: vec![],
    };
    run_node_body(
        &initial_label,
        Box::new(move |runtime| {
            let result = runtime.channel_create(&less_secret_label);
            assert_eq!(Err(OakStatus::ErrPermissionDenied), result);
            Ok(())
        }),
    );
}

/// Create a test Node that creates a Channel with a less secret label and succeeds.
#[test]
fn create_channel_more_secret_label_ok() {
    let initial_label = Label {
        secrecy_tags: vec![oak_abi::label::authorization_bearer_token_hmac_tag(&[
            1, 1, 1,
        ])],
        integrity_tags: vec![],
    };
    let more_secret_label = Label {
        secrecy_tags: vec![
            oak_abi::label::authorization_bearer_token_hmac_tag(&[1, 1, 1]),
            oak_abi::label::authorization_bearer_token_hmac_tag(&[2, 2, 2]),
        ],
        integrity_tags: vec![],
    };
    run_node_body(
        &initial_label,
        Box::new(move |runtime| {
            let result = runtime.channel_create(&more_secret_label);
            assert_eq!(true, result.is_ok());
            Ok(())
        }),
    );
}

/// Create a test Node that creates a Node with the same label and succeeds.
#[test]
fn create_node_same_label_ok() {
    let label = test_label();
    let label_clone = label.clone();
    run_node_body(
        &label,
        Box::new(move |runtime| {
            let (_write_handle, read_handle) = runtime.channel_create(&label_clone)?;
            let result = runtime.node_create("log", "unused", &label_clone, read_handle);
            assert_eq!(Ok(()), result);
            Ok(())
        }),
    );
}

/// Create a test Node that creates a Node with a non-existing configuration name and fails.
#[test]
fn create_node_invalid_configuration_err() {
    let label = test_label();
    let label_clone = label.clone();
    run_node_body(
        &label,
        Box::new(move |runtime| {
            let (_write_handle, read_handle) = runtime.channel_create(&label_clone)?;
            let result = runtime.node_create(
                "invalid-configuration-name",
                "unused",
                &label_clone,
                read_handle,
            );
            assert_eq!(Err(OakStatus::ErrInvalidArgs), result);
            Ok(())
        }),
    );
}

/// Create a test Node that creates a Node with a less secret label and fails.
///
/// If this succeeded, it would be a violation of information flow control, since the original
/// secret Node would be able to spawn "less secret / public" Nodes and use their side effects as a
/// covert channel to exfiltrate secret data.
#[test]
fn create_node_less_secret_label_err() {
    let initial_label = Label {
        secrecy_tags: vec![oak_abi::label::authorization_bearer_token_hmac_tag(&[
            1, 1, 1,
        ])],
        integrity_tags: vec![],
    };
    let less_secret_label = Label {
        secrecy_tags: vec![],
        integrity_tags: vec![],
    };
    let initial_label_clone = initial_label.clone();
    run_node_body(
        &initial_label,
        Box::new(move |runtime| {
            let (_write_handle, read_handle) = runtime.channel_create(&initial_label_clone)?;
            let result = runtime.node_create("log", "unused", &less_secret_label, read_handle);
            assert_eq!(Err(OakStatus::ErrPermissionDenied), result);
            Ok(())
        }),
    );
}

/// Create a test Node that creates a Node with a more secret label and succeeds.
#[test]
fn create_node_more_secret_label_ok() {
    let initial_label = Label {
        secrecy_tags: vec![oak_abi::label::authorization_bearer_token_hmac_tag(&[
            1, 1, 1,
        ])],
        integrity_tags: vec![],
    };
    let more_secret_label = Label {
        secrecy_tags: vec![
            oak_abi::label::authorization_bearer_token_hmac_tag(&[1, 1, 1]),
            oak_abi::label::authorization_bearer_token_hmac_tag(&[2, 2, 2]),
        ],
        integrity_tags: vec![],
    };
    let initial_label_clone = initial_label.clone();
    run_node_body(
        &initial_label,
        Box::new(move |runtime| {
            let (_write_handle, read_handle) = runtime.channel_create(&initial_label_clone)?;
            let result = runtime.node_create("log", "unused", &more_secret_label, read_handle);
            assert_eq!(Ok(()), result);
            Ok(())
        }),
    );
}

#[test]
fn wait_on_channels_immediately_returns_if_any_channel_is_orphaned() {
    let label = test_label();
    let label_clone = label.clone();
    run_node_body(
        &label,
        Box::new(move |runtime| {
            let (write_handle_0, read_handle_0) = runtime.channel_create(&label_clone)?;
            let (_write_handle_1, read_handle_1) = runtime.channel_create(&label_clone)?;

            // Close the write_handle; this should make the channel Orphaned
            let result = runtime.channel_close(write_handle_0);
            assert_eq!(Ok(()), result);

            let result = runtime.wait_on_channels(&[read_handle_0, read_handle_1]);
            assert_eq!(
                Ok(vec![
                    ChannelReadStatus::Orphaned,
                    ChannelReadStatus::NotReady
                ]),
                result
            );
            Ok(())
        }),
    );
}

#[test]
fn wait_on_channels_blocks_if_all_channels_have_status_not_ready() {
    let label = test_label();
    let label_clone = label.clone();
    run_node_body(
        &label,
        Box::new(move |runtime| {
            let (write_handle, read_handle) = runtime.channel_create(&label_clone)?;

            // Change the status of the channel concurrently, to unpark the waiting thread.
            let runtime_copy = runtime.clone();
            let start = std::time::Instant::now();
            std::thread::spawn(move || {
                let ten_millis = std::time::Duration::from_millis(10);
                thread::sleep(ten_millis);

                // Close the write_handle; this should make the channel Orphaned
                let result = runtime_copy.channel_close(write_handle);
                assert_eq!(Ok(()), result);
            });

            let result = runtime.wait_on_channels(&[read_handle]);
            assert!(start.elapsed() >= std::time::Duration::from_millis(10));
            assert_eq!(Ok(vec![ChannelReadStatus::Orphaned]), result);
            Ok(())
        }),
    );
}

#[test]
fn wait_on_channels_immediately_returns_if_any_channel_is_invalid() {
    let label = test_label();
    let label_clone = label.clone();
    run_node_body(
        &label,
        Box::new(move |runtime| {
            let (write_handle, _read_handle) = runtime.channel_create(&label_clone)?;
            let (_write_handle, read_handle) = runtime.channel_create(&label_clone)?;

            let result = runtime.wait_on_channels(&[write_handle, read_handle]);
            assert_eq!(
                Ok(vec![
                    ChannelReadStatus::InvalidChannel,
                    ChannelReadStatus::NotReady
                ]),
                result
            );
            Ok(())
        }),
    );
}

#[test]
fn wait_on_channels_immediately_returns_if_the_input_list_is_empty() {
    let label = test_label();
    run_node_body(
        &label,
        Box::new(|runtime| {
            let result = runtime.wait_on_channels(&[]);
            assert_eq!(Ok(Vec::<ChannelReadStatus>::new()), result);
            Ok(())
        }),
    );
}
