//
// Copyright 2026 The Project Oak Authors
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

#![no_std]

extern crate alloc;
use alloc::{vec, vec::Vec};
use core::{default::Default, marker::PhantomData};

use oak_channel::{Read, Write};
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_session::{ClientSession, ProtocolEngine, ServerSession, Session, config::SessionConfig};
use prost::Message;

// A trait for reading/writing length-prefixed messages.
pub trait MessageStream {
    fn send_message(&mut self, msg: &[u8]);
    fn read_message(&mut self) -> Vec<u8>;
}

impl<T: Read + Write> MessageStream for T {
    fn read_message(&mut self) -> Vec<u8> {
        let mut size_buf = [0u8; 4];
        self.read_exact(&mut size_buf).expect("failed to read message size");
        let size = u32::from_le_bytes(size_buf) as usize;
        let mut buf = vec![0u8; size];
        self.read_exact(&mut buf).expect("failed to read message");
        buf
    }

    fn send_message(&mut self, msg: &[u8]) {
        let size = msg.len() as u32;
        self.write_all(&size.to_le_bytes()).expect("failed to write message size");
        self.write_all(msg).expect("failed to write message");
    }
}

// A message stream implemented as a noise session over a message stream.
pub struct NoiseMessageStream<MS: MessageStream, I, O, S>
where
    I: prost::Message + Default,
    O: prost::Message + Default,
    S: ProtocolEngine<I, O> + Session,
{
    message_stream: MS,
    session: S,
    _phantom_i: PhantomData<I>,
    _phantom_o: PhantomData<O>,
}

pub type ClientNoiseMessageStream<MS> =
    NoiseMessageStream<MS, SessionResponse, SessionRequest, ClientSession>;
pub type ServerNoiseMessageStream<MS> =
    NoiseMessageStream<MS, SessionRequest, SessionResponse, ServerSession>;

impl<MS: MessageStream> ClientNoiseMessageStream<MS> {
    // Create a new client session for the provided message stream, and perform
    // handshake. Unattested NoiseNN is used.
    pub fn new_client(mut message_stream: MS) -> ClientNoiseMessageStream<MS> {
        let mut session = ClientSession::create(
            SessionConfig::builder(
                oak_session::attestation::AttestationType::Unattested,
                oak_session::handshake::HandshakeType::NoiseNN,
            )
            .build(),
        )
        .unwrap();
        while !session.is_open() {
            let init_req = session
                .get_outgoing_message()
                .expect("failed to get outgoing handshake message")
                .expect("expected outgoing message");
            message_stream.send_message(init_req.encode_to_vec().as_slice());
            if !session.is_open() {
                let resp_msg = message_stream.read_message();
                let session_response = SessionResponse::decode(resp_msg.as_slice())
                    .expect("failed to decode session response");
                session
                    .put_incoming_message(session_response)
                    .expect("failed to put incoming message");
            }
        }
        NoiseMessageStream {
            message_stream,
            session,
            _phantom_i: PhantomData,
            _phantom_o: PhantomData,
        }
    }
}

impl<MS: MessageStream> ServerNoiseMessageStream<MS> {
    // Create a new server session for the provided message stream, and perform
    // handshake. Unattested NoiseNN is used.
    pub fn new_server(mut message_stream: MS) -> ServerNoiseMessageStream<MS> {
        let mut session = ServerSession::create(
            SessionConfig::builder(
                oak_session::attestation::AttestationType::Unattested,
                oak_session::handshake::HandshakeType::NoiseNN,
            )
            .build(),
        )
        .unwrap();
        while !session.is_open() {
            let req_bytes = message_stream.read_message();
            let session_req = SessionRequest::decode(req_bytes.as_slice())
                .expect("failed to decode incoming request");
            session.put_incoming_message(session_req).expect("failed to put incoming message");
            if !session.is_open() {
                let resp = session
                    .get_outgoing_message()
                    .expect("failed to get outgoing handshake response message")
                    .expect("expected outgoing message");
                message_stream.send_message(resp.encode_to_vec().as_slice());
            }
        }
        NoiseMessageStream {
            message_stream,
            session,
            _phantom_i: PhantomData,
            _phantom_o: PhantomData,
        }
    }
}

/// The implementation of MessageStream for NoiseMessageStream reads and
/// writes messages from the wrapped [`MessageStream`], and uses the wrapped
/// [`Session`] to encrypt/decrypt the bytes.
///
/// The length encoding is outside of the encrypted payload, so that reading can
/// occur as expected.
impl<MS: MessageStream, I, O, S> MessageStream for NoiseMessageStream<MS, I, O, S>
where
    I: prost::Message + Default,
    O: prost::Message + Default,
    S: ProtocolEngine<I, O> + Session,
{
    fn read_message(&mut self) -> Vec<u8> {
        let incoming_bytes = self.message_stream.read_message();
        let incoming_message = <I as prost::Message>::decode(incoming_bytes.as_slice())
            .expect("failed to decode incoming encrypted message");
        self.session
            .put_incoming_message(incoming_message)
            .expect("failed to put incoming message");
        self.session
            .read()
            .expect("failed to read decrypted message")
            .expect("empty decrypted message")
            .plaintext
    }

    fn send_message(&mut self, msg: &[u8]) {
        self.session
            .write(PlaintextMessage { plaintext: msg.to_vec() })
            .expect("failed to write plaintext message");
        let outgoing_message = self
            .session
            .get_outgoing_message()
            .expect("failed to get outgoing encrypted message")
            .expect("expected outgoing message");
        let outgoing_bytes = outgoing_message.encode_to_vec();
        self.message_stream.send_message(outgoing_bytes.as_slice());
    }
}
