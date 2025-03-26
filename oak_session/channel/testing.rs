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

use std::{
    marker::PhantomData,
    sync::{Arc, Mutex},
};

use oak_proto_rust::oak::session::v1::PlaintextMessage;
use oak_session_channel::{ProtocolSession, Transport};

/// A simple mock peer (client or server) that can store received messages and
/// receive messages to send back to the client.
struct MockPeer {
    received_messages: Vec<Vec<u8>>,
    messages_to_send: Vec<Vec<u8>>,
}

/// Controls for a mock server instance (used by a test transport that interacts
/// with the server).
pub struct MockPeerControl {
    peer: Arc<Mutex<MockPeer>>,
}

/// Verificaiton methods for a mock server instance (used by transport tests).
pub struct MockPeerVerification {
    peer: Arc<Mutex<MockPeer>>,
}

/// Create a new mock server and return a control/verification pair for it.
fn mock_peer() -> (MockPeerControl, MockPeerVerification) {
    let peer =
        Arc::new(Mutex::new(MockPeer { received_messages: vec![], messages_to_send: vec![] }));
    (MockPeerControl { peer: peer.clone() }, MockPeerVerification { peer: peer.clone() })
}

impl MockPeerControl {
    /// The server can call this to add messages that it receives from the
    /// channel.
    pub fn add_received_message(&mut self, msg: Vec<u8>) {
        self.peer.lock().expect("failed to lock server").received_messages.push(msg)
    }

    /// The server can use this to add the next message to send via the
    /// transport. If the test has not added any message this will panic.
    pub fn get_message_to_send(&mut self) -> Vec<u8> {
        self.peer
            .lock()
            .expect("failed to lock server")
            .messages_to_send
            .pop()
            .expect("no message to send")
    }
}

impl MockPeerVerification {
    /// The tests can call this to get all messages received by the server so
    /// far.
    pub fn get_received_messages(&mut self) -> Vec<Vec<u8>> {
        std::mem::take(&mut self.peer.lock().expect("failed to lock server").received_messages)
    }

    /// The tests can use this to add a message to send back to the client. The
    /// next time the transport tries to receive a message, the oldest
    /// queued message will be sent.
    pub fn add_message_to_send(&mut self, msg: Vec<u8>) {
        self.peer.lock().expect("failed to lock server").messages_to_send.push(msg);
    }
}

/// A simple [`Transport`] implementation that wraps a [`MockServer`] and passes
/// messages to/from it. The [`MockServer`] can also be accessed by tests for
/// validation purposes.
pub struct TestTransport<I: Send, O: Send, PS: ProtocolSession<I, O>> {
    peer_session: PS,
    mock_peer_control: MockPeerControl,
    _phantom_i: PhantomData<I>,
    _phantom_o: PhantomData<O>,
}

#[async_trait::async_trait]
impl<I: Send, O: Send, PS: ProtocolSession<I, O>> Transport for TestTransport<I, O, PS> {
    type OutgoingMessage = I;
    type IncomingMessage = O;
    type Error = anyhow::Error;

    async fn send(&mut self, message: Self::OutgoingMessage) -> anyhow::Result<()> {
        self.peer_session.put_incoming_message(message)?;
        if self.peer_session.is_open() {
            let received = self.peer_session.read().expect("failed to read a server message");
            if let Some(received) = received {
                self.mock_peer_control.add_received_message(received.plaintext);
            }
        }
        Ok(())
    }

    async fn receive(&mut self) -> anyhow::Result<Self::IncomingMessage> {
        if self.peer_session.is_open() {
            let outgoing =
                PlaintextMessage { plaintext: self.mock_peer_control.get_message_to_send() };
            self.peer_session.write(outgoing).expect("failed to write outgoing message");
        }
        self.peer_session
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
pub fn test_transport<I: Send, O: Send, PS: ProtocolSession<I, O>>(
    peer_session: PS,
) -> (TestTransport<I, O, PS>, MockPeerVerification) {
    let (mock_peer_control, mock_peer_verification) = mock_peer();
    (
        TestTransport {
            peer_session,
            mock_peer_control,
            _phantom_i: PhantomData,
            _phantom_o: PhantomData,
        },
        mock_peer_verification,
    )
}
