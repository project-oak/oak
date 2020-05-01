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

type NodeBody = dyn Fn(RuntimeProxy) -> Result<(), OakStatus> + Send + Sync;

/// Runs the provided function as if it were the body of a [`Node`] implementation, which is
/// instantiated by the [`Runtime`] with the provided [`Label`].
fn run_node_body(node_label: Label, node_body: Box<NodeBody>) {
    let configuration = crate::runtime::Configuration {
        nodes: maplit::hashmap![
            "log".to_string() => crate::node::Configuration::LogNode,
        ],
        entry_module: "test_module".to_string(),
        entrypoint: "test_function".to_string(),
    };
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
    let test_proxy = proxy.clone().runtime.proxy_for_new_node();
    let new_node_id = test_proxy.node_id;
    let new_node_name = format!("TestNode({})", new_node_id.0);
    proxy
        .runtime
        .node_configure_instance(new_node_id, "test_module.test_function", &node_label);

    let node_instance = TestNode { node_body };
    let result = proxy.runtime.node_start_instance(
        &new_node_name,
        Box::new(node_instance),
        test_proxy,
        oak_abi::INVALID_HANDLE,
    );
    assert_eq!(Ok(()), result);
}

/// Create a test Node that creates a channel and succeeds.
#[test]
fn create_channel_success() {
    run_node_body(
        Label::public_trusted(),
        Box::new(|runtime| {
            // Attempt to perform an operation that requires the [`Runtime`] to have created an
            // appropriate [`NodeInfo`] instance.
            let (_write_handle, _read_handle) = runtime.channel_create(&Label::public_trusted());
            Ok(())
        }),
    );
}

/// Create a test Node that creates a Node and succeeds.
#[test]
fn create_node_success() {
    run_node_body(
        Label::public_trusted(),
        Box::new(|runtime| {
            let (_write_handle, read_handle) = runtime.channel_create(&Label::public_trusted());
            let result =
                runtime.node_create("log", "unused", &Label::public_trusted(), read_handle);
            assert_eq!(Ok(()), result);
            Ok(())
        }),
    );
}

/// Create a test Node that creates a Node with a non-existing configuration name and fails.
#[test]
fn create_node_invalid_configuration() {
    run_node_body(
        Label::public_trusted(),
        Box::new(|runtime| {
            let (_write_handle, read_handle) = runtime.channel_create(&Label::public_trusted());
            let result = runtime.node_create(
                "invalid-configuration-name",
                "unused",
                &Label::public_trusted(),
                read_handle,
            );
            assert_eq!(Err(OakStatus::ErrInvalidArgs), result);
            Ok(())
        }),
    );
}

/// Create a test Node that creates a Node with a more public label and fails.
///
/// If this succeeded, it would be a violation of information flow control, since the original
/// secret Node would be able to spawn "public" Nodes and use their side effects as a covert
/// channel to exfiltrate secret data.
#[test]
fn create_node_more_public_label() {
    let secret_label = Label {
        secrecy_tags: vec![oak_abi::label::authorization_bearer_token_hmac_tag(&[
            1, 1, 1,
        ])],
        integrity_tags: vec![],
    };
    run_node_body(
        secret_label,
        Box::new(|runtime| {
            let (_write_handle, read_handle) = runtime.channel_create(&Label::public_trusted());
            let result =
                runtime.node_create("log", "unused", &Label::public_trusted(), read_handle);
            assert_eq!(Err(OakStatus::ErrPermissionDenied), result);
            Ok(())
        }),
    );
}

#[test]
fn wait_on_channels_immediately_returns_if_any_channel_is_orphaned() {
    run_node_body(
        Label::public_trusted(),
        Box::new(|runtime| {
            let (write_handle_0, read_handle_0) = runtime.channel_create(&Label::public_trusted());
            let (_write_handle_1, read_handle_1) = runtime.channel_create(&Label::public_trusted());

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
    run_node_body(
        Label::public_trusted(),
        Box::new(|runtime| {
            let (write_handle, read_handle) = runtime.channel_create(&Label::public_trusted());

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
    run_node_body(
        Label::public_trusted(),
        Box::new(|runtime| {
            let (write_handle, _read_handle) = runtime.channel_create(&Label::public_trusted());
            let (_write_handle, read_handle) = runtime.channel_create(&Label::public_trusted());

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
    run_node_body(
        Label::public_trusted(),
        Box::new(|runtime| {
            let result = runtime.wait_on_channels(&[]);
            assert_eq!(Ok(Vec::<ChannelReadStatus>::new()), result);
            Ok(())
        }),
    );
}
