//
// Copyright 2025 The Project Oak Authors
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
// A mock server to wrap with the test transport.

//! Utiltiies for testing session channels.

use std::sync::{Arc, Mutex};

use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_session::{ProtocolEngine, ServerSession, Session};
use oak_session_channel::Transport;

/// A simple mock server that can store received messages and receive messages
/// to send back to the client.
struct MockServer {
    received_messages: Vec<Vec<u8>>,
    messages_to_send: Vec<Vec<u8>>,
}

/// Controls for a mock server instance (used by a test transport that interacts
/// with the server).
pub struct MockServerControl {
    server: Arc<Mutex<MockServer>>,
}

/// Verificaiton methods for a mock server instance (used by transport tests).
pub struct MockServerVerification {
    server: Arc<Mutex<MockServer>>,
}

/// Create a new mock server and return a control/verification pair for it.
fn mock_server() -> (MockServerControl, MockServerVerification) {
    let server =
        Arc::new(Mutex::new(MockServer { received_messages: vec![], messages_to_send: vec![] }));
    (
        MockServerControl { server: server.clone() },
        MockServerVerification { server: server.clone() },
    )
}

impl MockServerControl {
    /// The server can call this to add messages that it receives from the
    /// channel.
    pub fn add_received_message(&mut self, msg: Vec<u8>) {
        self.server.lock().expect("failed to lock server").received_messages.push(msg)
    }

    /// The server can use this to add the next message to send via the
    /// transport. If the test has not added any message this will panic.
    pub fn get_message_to_send(&mut self) -> Vec<u8> {
        self.server
            .lock()
            .expect("failed to lock server")
            .messages_to_send
            .pop()
            .expect("no message to send")
    }
}

impl MockServerVerification {
    /// The tests can call this to get all messages received by the server so
    /// far.
    pub fn get_received_messages(&mut self) -> Vec<Vec<u8>> {
        std::mem::take(&mut self.server.lock().expect("failed to lock server").received_messages)
    }

    /// The tests can use this to add a message to send back to the client. The
    /// next time the transport tries to receive a message, the oldest
    /// queued message will be sent.
    pub fn add_message_to_send(&mut self, msg: Vec<u8>) {
        self.server.lock().expect("failed to lock server").messages_to_send.push(msg);
    }
}

/// A simple [`Transport`] implementation that wraps a [`MockServer`] and passes
/// messages to/from it. The [`MockServer`] can also be accessed by tests for
/// validation purposes.
pub struct TestTransport {
    server_session: ServerSession,
    mock_server_control: MockServerControl,
}

#[async_trait::async_trait]
impl Transport for TestTransport {
    type OutgoingMessage = SessionRequest;
    type IncomingMessage = SessionResponse;
    type Error = anyhow::Error;

    async fn send(&mut self, message: Self::OutgoingMessage) -> anyhow::Result<()> {
        self.server_session.put_incoming_message(&message)?;
        let received = self
            .server_session
            .read()
            .expect("failed to read a server message")
            .expect("empty read result");
        self.mock_server_control.add_received_message(received.plaintext);
        Ok(())
    }

    async fn receive(&mut self) -> anyhow::Result<Self::IncomingMessage> {
        let outgoing =
            PlaintextMessage { plaintext: self.mock_server_control.get_message_to_send() };
        self.server_session.write(&outgoing).expect("failed to write outgoing message");
        self.server_session
            .get_outgoing_message()
            .transpose()
            .ok_or_else(|| anyhow::anyhow!("unexpected empty message"))?
    }
}

/// Create a new test transport.
///
/// Creates a new mock server control/verification pair, and returns a transport
/// wrapping the control portion, and returns the verification portion to the
/// caller for use in test assertions.
pub fn test_transport(server_session: ServerSession) -> (TestTransport, MockServerVerification) {
    let (mock_server_control, mock_server_verification) = mock_server();
    (TestTransport { server_session, mock_server_control }, mock_server_verification)
}
