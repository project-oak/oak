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
// Needed only to inspect `std::io::Error` for end-of-stream; see
// `is_end_of_stream`. The crate stays `no_std` for the enclave build.
#[cfg(feature = "std")]
extern crate std;

use alloc::{vec, vec::Vec};
use core::default::Default;

use oak_channel::{Read, Write, message::ResponseMessage, server::ServerChannelHandle};
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_session::{ClientSession, ProtocolEngine, ServerSession, Session, config::SessionConfig};
use prost::Message;

/// Control messages understood by every benchmark echo server.
///
/// The servers echo any payload that is not one of these straight back. The
/// sentinels are how a client says it has finished with a channel, which only
/// became necessary once the benchmarks started reusing a channel across many
/// exchanges instead of building a fresh one per message.
///
/// The benchmark's own payloads cannot collide with these. `create_message`
/// fills a buffer with `0, 1, 2, ...`, so a four-byte payload is
/// `[0, 1, 2, 3]`, never `b"exit"`.
pub mod control {
    /// Asks the server to stop serving the current channel.
    ///
    /// The server echoes it back *before* acting, so the client can tell the
    /// cycle completed. That acknowledgement is not a nicety. The Restricted
    /// Kernel leg has no connection to close and no end-of-stream to observe,
    /// so a client that simply walked away would leave the enclave blocked
    /// reading an application message while the client sent the first frame
    /// of a new handshake.
    ///
    /// Afterwards the TCP legs return to `accept`, and the Restricted Kernel
    /// Noise leg discards its session and waits for a fresh handshake.
    pub const CLOSE: &[u8] = b"close";

    /// Asks the server to exit altogether.
    ///
    /// Only used by the legs whose server the harness owns and must join.
    /// The server does not echo this one; the connection dropping is the
    /// acknowledgement.
    pub const EXIT: &[u8] = b"exit";
}

/// A bidirectional stream of length-prefixed messages.
///
/// Implementations exist for anything that is [`oak_channel::Read`] plus
/// [`oak_channel::Write`] (so a `TcpStream` or a `rustls::StreamOwned`
/// qualifies), for the Restricted Kernel channel at either end, and for a
/// Noise session layered over any of those.
pub trait MessageStream {
    fn send_message(&mut self, msg: &[u8]);

    /// Reads one message, or returns `None` if the peer closed the stream
    /// cleanly -- that is, at a message boundary, having sent nothing.
    ///
    /// Servers must use this. An echo server is shared by every iteration of
    /// a benchmark, and clients come and go; a client that exits without
    /// sending [`control::CLOSE`] is untidy but it must not take the server
    /// thread down, because the resulting panic surfaces much later as an
    /// unrelated failure in whichever leg runs next.
    ///
    /// Transports with no notion of end-of-stream -- the Restricted Kernel
    /// channel is one, being a pair of file descriptors into a running
    /// enclave rather than a connection -- never return `None`.
    fn try_read_message(&mut self) -> Option<Vec<u8>>;

    /// Reads one message, panicking if the peer has gone away.
    ///
    /// Clients use this: the server is part of the harness, so its
    /// disappearance is a bug rather than a condition worth handling.
    fn read_message(&mut self) -> Vec<u8> {
        self.try_read_message().expect("peer closed the stream")
    }
}

pub struct OakServerChannelMessageStream {
    oak_server_channel: ServerChannelHandle,
}

impl OakServerChannelMessageStream {
    pub fn new(oak_server_channel: ServerChannelHandle) -> Self {
        OakServerChannelMessageStream { oak_server_channel }
    }
}

impl MessageStream for OakServerChannelMessageStream {
    /// Never `None`: the enclave channel is a pair of file descriptors, not a
    /// connection, so there is nothing that could close.
    fn try_read_message(&mut self) -> Option<Vec<u8>> {
        let (msg, _timer) = self.oak_server_channel.read_request().expect("reading message");
        Some(msg.body)
    }

    fn send_message(&mut self, msg: &[u8]) {
        self.oak_server_channel
            .write_response(ResponseMessage { invocation_id: 0, body: msg.to_vec() })
            .expect("writing message");
    }
}

/// Reports whether a [`oak_channel::Read`] failure was a clean end of stream.
///
/// `oak_channel`'s blanket implementation over [`std::io::Read`] wraps the
/// underlying error with `anyhow::Error::msg`, which keeps the concrete type
/// recoverable by downcast. A short read at a message boundary arrives as
/// [`std::io::ErrorKind::UnexpectedEof`].
///
/// Without `std` there is no such error to inspect, and the transports that
/// remain -- the Restricted Kernel channel -- cannot reach end of stream
/// anyway, so every failure is a real one.
#[cfg(feature = "std")]
fn is_end_of_stream(err: &anyhow::Error) -> bool {
    err.downcast_ref::<std::io::Error>()
        .is_some_and(|e| e.kind() == std::io::ErrorKind::UnexpectedEof)
}

#[cfg(not(feature = "std"))]
fn is_end_of_stream(_err: &anyhow::Error) -> bool {
    false
}

impl<T: Read + Write> MessageStream for T {
    fn try_read_message(&mut self) -> Option<Vec<u8>> {
        let mut size_buf = [0u8; 4];
        match self.read_exact(&mut size_buf) {
            Ok(()) => {}
            // Only a failure to read the *length* can be a clean close. Once a
            // length has arrived the peer has committed to a body, so a short
            // read there is a truncated message and a real error.
            Err(err) if is_end_of_stream(&err) => return None,
            Err(err) => panic!("reading message size: {err}"),
        }
        let size = u32::from_le_bytes(size_buf) as usize;
        let mut buf = vec![0u8; size];
        self.read_exact(&mut buf).expect("reading message");
        Some(buf)
    }

    /// Writes the length prefix and the body as a single `write_all`.
    ///
    /// Not a micro-optimisation. Every leg shares this framing but sits at a
    /// different level relative to it. The Noise legs encrypt above it, so two
    /// writes cost two syscalls. The TLS legs wrap this stream in a
    /// `rustls::StreamOwned`, whose `write` forms a record and then calls
    /// `complete_io`, so a length write followed by a body write became **two
    /// TLS records** -- two AEAD seals and two sets of record overhead, doubled
    /// again on the read side -- for every message a Noise leg sealed once.
    ///
    /// Measured on the local TCP legs, one write versus two:
    ///
    /// | leg | two writes | one write | change |
    /// | --- | ---: | ---: | ---: |
    /// | plaintext | 10.730 µs | 8.660 µs | -2.07 µs |
    /// | Noise | 11.644 µs | 9.571 µs | -2.07 µs |
    /// | TLS | 14.629 µs | 7.721 µs | -6.91 µs |
    ///
    /// Plaintext and Noise save an identical 2.07 µs, which is the two `sendto`
    /// calls this removes (`strace -c` confirms 4 per exchange before and 2
    /// after, with reads unchanged) and puts a syscall on this host at about
    /// 1.03 µs. TLS saves 3.3x that, and the surplus is the second record's
    /// crypto. So most of what looked like TLS overhead was this framing.
    ///
    /// The cost is one allocation and one copy per message, charged identically
    /// to every leg.
    ///
    /// # This does not make the legs comparable
    ///
    /// It removes one asymmetry and exposes another. With a single record,
    /// rustls serves the second `read_exact` out of `received_plaintext`, so
    /// the TLS legs now issue **4** socket syscalls per exchange against
    /// plaintext's **6** (measured: 2.34 versus 4.55 reads per exchange). At
    /// 1.03 µs each that is 2.06 µs in TLS's favour, against roughly 1.1 µs of
    /// AEAD work, which is why TLS now reports *faster than plaintext* -- an
    /// impossible result that is entirely an artefact of read buffering.
    ///
    /// The two-write framing was accidentally syscall-symmetric (8 per exchange
    /// on every leg) while being crypto-asymmetric. This is the reverse. Making
    /// the comparison fair needs a buffered reader on the plaintext and Noise
    /// legs so that every leg performs one socket read per message, which TLS
    /// gets for free because it must buffer records.
    ///
    /// Note also that rustls writes with `writev` while the raw legs use
    /// `sendto`. That difference is not controlled for, and on this host the
    /// `write` family has been measured as materially more expensive than the
    /// `send` family.
    fn send_message(&mut self, msg: &[u8]) {
        let mut frame = Vec::with_capacity(size_of::<u32>() + msg.len());
        frame.extend_from_slice(&(msg.len() as u32).to_le_bytes());
        frame.extend_from_slice(msg);
        self.write_all(&frame).expect("writing message");
    }
}

// A message stream implemented as a noise session over a message stream.
pub struct NoiseMessageStream<MS: MessageStream, S>
where
    S: ProtocolEngine + Session,
{
    message_stream: MS,
    session: S,
}

pub type ClientNoiseMessageStream<MS> = NoiseMessageStream<MS, ClientSession>;
pub type ServerNoiseMessageStream<MS> = NoiseMessageStream<MS, ServerSession>;

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
        NoiseMessageStream { message_stream, session }
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
        NoiseMessageStream { message_stream, session }
    }
}

/// The implementation of MessageStream for NoiseMessageStream reads and
/// writes messages from the wrapped [`MessageStream`], and uses the wrapped
/// [`Session`] to encrypt/decrypt the bytes.
///
/// The length encoding is outside of the encrypted payload, so that reading can
/// occur as expected.
impl<MS: MessageStream, S> MessageStream for NoiseMessageStream<MS, S>
where
    S: ProtocolEngine + Session,
    S::Input: prost::Message + Default,
    S::Output: prost::Message,
{
    /// Propagates the inner stream's end of stream. A Noise session over a
    /// transport that has closed cannot produce another message, and the
    /// session state is not worth preserving.
    fn try_read_message(&mut self) -> Option<Vec<u8>> {
        let incoming_bytes = self.message_stream.try_read_message()?;
        let incoming_message = <S::Input as prost::Message>::decode(incoming_bytes.as_slice())
            .expect("decoding incoming encrypted message");
        self.session.put_incoming_message(incoming_message).expect("putting incoming message");
        Some(
            self.session
                .read()
                .expect("reading decrypted message")
                .expect("empty decrypted message")
                .plaintext,
        )
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
