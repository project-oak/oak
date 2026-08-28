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

/// A stream that reads through a buffer and writes straight through.
///
/// Every leg must issue the same number of socket calls per message, or the
/// benchmark measures syscall counts instead of cryptography. At a one-byte
/// payload a syscall costs about 1.03 µs on the reference host, far more than
/// the AEAD work, so an unmatched read dominates the result. Unbuffered, the
/// length read and the body read are two separate `recvfrom` calls; buffered,
/// they are one.
///
/// Each leg wraps its own stream, and *where* it wraps matters. Put this
/// directly above whatever produces message bytes: the socket for the raw legs,
/// the `rustls::StreamOwned` for the TLS legs. Underneath rustls it would
/// instead coalesce rustls's own 4 KiB record reads and copy every byte of
/// ciphertext, which changes the count being reported.
///
/// Writes deliberately pass straight through. Buffering them would need an
/// explicit flush per message to preserve the request/response shape, which is
/// the same syscall count with an extra copy.
#[cfg(feature = "std")]
pub struct BufferedStream<S: std::io::Read + std::io::Write> {
    inner: std::io::BufReader<S>,
}

#[cfg(feature = "std")]
impl<S: std::io::Read + std::io::Write> BufferedStream<S> {
    pub fn new(inner: S) -> Self {
        BufferedStream { inner: std::io::BufReader::new(inner) }
    }

    /// Borrows the wrapped stream, for setting or inspecting socket options.
    pub fn get_ref(&self) -> &S {
        self.inner.get_ref()
    }
}

#[cfg(feature = "std")]
impl<S: std::io::Read + std::io::Write> std::io::Read for BufferedStream<S> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.inner.read(buf)
    }
}

#[cfg(feature = "std")]
impl<S: std::io::Read + std::io::Write> std::io::Write for BufferedStream<S> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.inner.get_mut().write(buf)
    }

    /// Forwarded deliberately. The default implementation writes only the first
    /// slice, which would turn rustls's single vectored record write into a
    /// loop of one-slice writes and change the leg's syscall count -- the exact
    /// thing this type exists to hold constant.
    fn write_vectored(&mut self, bufs: &[std::io::IoSlice<'_>]) -> std::io::Result<usize> {
        self.inner.get_mut().write_vectored(bufs)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.get_mut().flush()
    }
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
    /// # On its own this did not make the legs comparable
    ///
    /// It removed one asymmetry and exposed another. With a single record,
    /// rustls served the second `read_exact` out of `received_plaintext`, so
    /// the TLS legs issued **4** socket syscalls per exchange against
    /// plaintext's **6** (measured: 2.34 versus 4.55 reads per exchange). At
    /// 1.03 µs each that is 2.06 µs in TLS's favour, against roughly 1.1 µs of
    /// AEAD work, which made TLS report *faster than plaintext* -- an
    /// impossible result that was entirely an artefact of read buffering.
    ///
    /// The two-write framing was accidentally syscall-symmetric (8 per exchange
    /// on every leg) while being crypto-asymmetric; one write is the reverse.
    /// `BufferedStream` closes the gap by giving every leg one socket read
    /// per message.
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

#[cfg(all(test, feature = "std"))]
mod tests {
    use std::{
        io::{IoSlice, Write as _},
        vec,
        vec::Vec,
    };

    use googletest::prelude::*;

    use super::*;

    /// A stream that counts the calls made to it.
    ///
    /// The two claims this module exists to check -- one write and one read per
    /// message -- are claims about *call counts*, not about bytes, so the
    /// counts are what the mock records. Reads are served from `to_read` and
    /// never span more than one call's worth of data, which is what a socket
    /// does.
    #[derive(Default)]
    struct CountingStream {
        to_read: Vec<u8>,
        read_pos: usize,
        reads: usize,
        written: Vec<u8>,
        writes: usize,
        /// Lengths passed to each `write_vectored`, so a forwarded vectored
        /// write can be told apart from a loop of single-slice writes.
        vectored_slice_counts: Vec<usize>,
    }

    impl CountingStream {
        fn with_input(to_read: Vec<u8>) -> Self {
            CountingStream { to_read, ..Default::default() }
        }
    }

    impl std::io::Read for CountingStream {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            self.reads += 1;
            let n = core::cmp::min(buf.len(), self.to_read.len() - self.read_pos);
            buf[..n].copy_from_slice(&self.to_read[self.read_pos..self.read_pos + n]);
            self.read_pos += n;
            Ok(n)
        }
    }

    impl std::io::Write for CountingStream {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.writes += 1;
            self.written.extend_from_slice(buf);
            Ok(buf.len())
        }

        fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> std::io::Result<usize> {
            self.writes += 1;
            self.vectored_slice_counts.push(bufs.len());
            let mut n = 0;
            for b in bufs {
                self.written.extend_from_slice(b);
                n += b.len();
            }
            Ok(n)
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    /// A framed message, as `send_message` writes it.
    fn framed(payload: &[u8]) -> Vec<u8> {
        let mut v = (payload.len() as u32).to_le_bytes().to_vec();
        v.extend_from_slice(payload);
        v
    }

    #[googletest::test]
    fn send_message_writes_the_frame_once() {
        let mut stream = CountingStream::default();
        stream.send_message(&[7u8; 100]);

        // One write, not two: a length write followed by a body write would
        // become two TLS records on the rustls legs.
        expect_that!(stream.writes, eq(1));
        expect_that!(stream.written, eq(&framed(&[7u8; 100])));
    }

    #[googletest::test]
    fn unbuffered_read_costs_two_reads() {
        // The baseline the buffer exists to remove, pinned so that the
        // buffered case below is measuring something.
        let mut stream = CountingStream::with_input(framed(&[9u8; 100]));
        let msg = stream.try_read_message();

        expect_that!(msg, some(eq(&vec![9u8; 100])));
        expect_that!(stream.reads, eq(2));
    }

    #[googletest::test]
    fn buffered_read_costs_one_read() {
        let inner = CountingStream::with_input(framed(&[9u8; 100]));
        let mut stream = BufferedStream::new(inner);
        let msg = stream.try_read_message();

        expect_that!(msg, some(eq(&vec![9u8; 100])));
        expect_that!(stream.get_ref().reads, eq(1));
    }

    #[googletest::test]
    fn buffering_does_not_add_a_write() {
        let mut stream = BufferedStream::new(CountingStream::default());
        stream.send_message(&[1u8; 10]);

        expect_that!(stream.get_ref().writes, eq(1));
        expect_that!(stream.get_ref().written, eq(&framed(&[1u8; 10])));
    }

    #[googletest::test]
    fn vectored_writes_are_forwarded_whole() {
        // rustls writes a record as several slices in one `writev`. The
        // default `write_vectored` would write only the first, turning that
        // into a loop and changing the leg's syscall count.
        let mut stream = BufferedStream::new(CountingStream::default());
        let n = stream
            .write_vectored(&[IoSlice::new(b"abc"), IoSlice::new(b"de")])
            .expect("write_vectored");

        expect_that!(n, eq(5));
        expect_that!(stream.get_ref().vectored_slice_counts, eq(&vec![2usize]));
        expect_that!(stream.get_ref().written, eq(&b"abcde".to_vec()));
    }

    #[googletest::test]
    fn clean_end_of_stream_reads_none() {
        let mut stream = CountingStream::default();
        expect_that!(stream.try_read_message(), none());
    }

    #[googletest::test]
    fn a_message_survives_a_round_trip() {
        let mut writer = CountingStream::default();
        writer.send_message(b"hello");

        let mut reader = CountingStream::with_input(writer.written);
        expect_that!(reader.try_read_message(), some(eq(&b"hello".to_vec())));
    }
}
