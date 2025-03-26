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
//

use std::{fmt, result};

use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest, SessionResponse};
use oak_session::{
    config::SessionConfig, session::Session, ClientSession, ProtocolEngine, ServerSession,
};

/// A transport implementation for an [`OakSessionChannel`].
///
/// [`Transport`] instances describe how to send/receive messages over the wire
/// on behalf of the channel.
#[async_trait::async_trait]
pub trait Transport: Send {
    /// The type of the message that will be sent out from this transport.
    type OutgoingMessage: Send;
    /// The type of the message that will be received into this transport.
    type IncomingMessage: Send;
    /// The error type for failures in send or receive.
    type Error: Send;
    async fn send(&mut self, message: Self::OutgoingMessage) -> result::Result<(), Self::Error>;
    async fn receive(&mut self) -> result::Result<Self::IncomingMessage, Self::Error>;
}

/// A convenience trait combining [`Session`] and [`ProtocolEngine`] traits.
pub trait ProtocolSession<OutgoingMessage, IncomingMessage>:
    Session + ProtocolEngine<OutgoingMessage, IncomingMessage>
{
}

impl ProtocolSession<SessionResponse, SessionRequest> for ClientSession {}
impl ProtocolSession<SessionRequest, SessionResponse> for ServerSession {}

/// A channel for sending/receiving bytes on an established attested encryption
/// channel.
///
/// An OakSessionChannel combines a transport that communicates with a remote
/// session instance with a local session instance.
///
/// In order for the channel to be successfully created, the initailize sequence
/// (handshake + attestation) must have already occurred. In most cases you'll
/// want to acquire an instance of this from an [`OakSessionClient``], which
/// will take care of the initialization sequence for you.
pub struct OakSessionChannel<
    OutgoingMessage,
    IncomingMessage,
    TransportError,
    Tr: Transport<
        OutgoingMessage = OutgoingMessage,
        IncomingMessage = IncomingMessage,
        Error = TransportError,
    >,
> {
    transport: Box<Tr>,
    session: Box<dyn ProtocolSession<IncomingMessage, OutgoingMessage>>,
}

/// A kind of error that can be returned by an [`OakSessionChannel`].
#[derive(Debug)]
pub enum ErrorKind<E> {
    /// An error that occurred while interacting with the local session.
    Session(Box<anyhow::Error>),

    /// An error that occurred while interacting with the remote transport.
    Transport(Box<E>),

    // An error that occurred in the channel logic itself.
    Channel,
}

/// An error returned by the channel.
#[derive(Debug)]
#[allow(dead_code)]
pub struct Error<E> {
    kind: ErrorKind<E>,
    msg: String,
}

impl<E: std::fmt::Debug> std::fmt::Display for Error<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(formatter, "{self:?}")
    }
}

impl<E: std::fmt::Debug> Error<E> {
    /// Create a new error of the specified [`ErrorKind`] with the provided
    /// message.
    pub fn new(kind: ErrorKind<E>, msg: impl Into<String>) -> Self {
        Self { kind, msg: msg.into() }
    }

    /// Create a new [`ErrorKind::Channel`] error with the provided message.
    pub fn new_channel_error(msg: impl Into<String>) -> Self {
        Self::new(ErrorKind::Channel, msg)
    }

    pub fn new_transport_error(e: E, msg: impl Into<String>) -> Self {
        Self::new(ErrorKind::Transport(Box::new(e)), msg)
    }

    pub fn new_session_error(e: anyhow::Error, msg: impl Into<String>) -> Self {
        Self::new(ErrorKind::Session(Box::new(e)), msg)
    }

    /// Return the [`ErrorKind`] for this error.
    pub fn kind(&self) -> &ErrorKind<E> {
        &self.kind
    }
}

pub type Result<T, TransportError> = result::Result<T, Error<TransportError>>;

impl<
        OutgoingMessage,
        IncomingMessage,
        TransportError: std::fmt::Debug + 'static,
        Tr: Transport<
            OutgoingMessage = OutgoingMessage,
            IncomingMessage = IncomingMessage,
            Error = TransportError,
        >,
    > OakSessionChannel<OutgoingMessage, IncomingMessage, TransportError, Tr>
{
    pub fn create(
        transport: Box<Tr>,
        session: Box<dyn ProtocolSession<IncomingMessage, OutgoingMessage>>,
    ) -> Self {
        Self { transport, session }
    }

    /// Send the provided unecrypted bytes on the session channel.
    ///
    /// The provided bytes will be encrypted and send to the remote session via
    /// the transport provided at construction.
    pub async fn send(&mut self, bytes: &[u8]) -> Result<(), TransportError> {
        self.session
            .write(PlaintextMessage { plaintext: bytes.to_vec() })
            .into_session_result("failed to write outgoing message")?;

        let outgoing_message: OutgoingMessage = self
            .session
            .get_outgoing_message()
            .into_session_result("failed to get outgoing message")?
            .expect_non_empty("empty outgoing message")?;

        self.transport.send(outgoing_message).await.into_transport_result("failed to send")?;

        Ok(())
    }

    /// Receive and decrypt a message from the remote session.
    ///
    /// The function will suspend until a new message is available on the
    /// transport. The received message will be decrypted by the local session
    /// and returned to the caller.
    pub async fn receive(&mut self) -> Result<Vec<u8>, TransportError> {
        let incoming_message = self
            .transport
            .receive()
            .await
            .into_transport_result("failed to receive on transport")?;

        self.session
            .put_incoming_message(incoming_message)
            .into_session_result("failed to put incoming message")?;

        self.session
            .read()
            .into_session_result("failed to read incoming message")?
            .expect_non_empty("no message to read after putting incoming message")
            .map(|pt| pt.plaintext)
    }
}

pub async fn new_client_channel<T, E: Send + Sync + std::fmt::Debug + 'static>(
    config: SessionConfig,
    transport: T,
) -> Result<OakSessionChannel<SessionRequest, SessionResponse, E, T>, E>
where
    T: Transport<OutgoingMessage = SessionRequest, IncomingMessage = SessionResponse, Error = E>,
{
    let mut transport = transport;
    let mut session = ClientSession::create(config)
        .map_err(|e| Error::new_session_error(e, "failed to create session"))?;

    while !session.is_open() {
        let init_request = session
            .get_outgoing_message()
            .map_err(|e| Error::new_session_error(e, "failed to get init request"))?
            .ok_or_else(|| Error::new_channel_error("no init message available"))?;

        transport
            .send(init_request)
            .await
            .map_err(|e| Error::new_transport_error(e, "failed to send outgoing init request"))?;

        if session.is_open() {
            break;
        }

        let init_response = transport
            .receive()
            .await
            .map_err(|e| Error::new_transport_error(e, "failed to receive init response"))?;

        session
            .put_incoming_message(init_response)
            .map_err(|e| Error::new_session_error(e, "failed to accept init response"))?;
    }

    Ok(OakSessionChannel::create(Box::new(transport), Box::new(session)))
}

pub async fn new_server_channel<T, E: Send + Sync + std::fmt::Debug + 'static>(
    config: SessionConfig,
    transport: T,
) -> Result<OakSessionChannel<SessionResponse, SessionRequest, E, T>, E>
where
    T: Transport<OutgoingMessage = SessionResponse, IncomingMessage = SessionRequest, Error = E>,
{
    let mut transport = transport;
    let mut session = ServerSession::create(config)
        .map_err(|e| Error::new_session_error(e, "failed to create session"))?;

    while !session.is_open() {
        let incoming_init_request = transport
            .receive()
            .await
            .map_err(|e| Error::new_transport_error(e, "failed to receive init request"))?;

        session
            .put_incoming_message(incoming_init_request)
            .map_err(|e| Error::new_session_error(e, "failed to accept init request"))?;

        if session.is_open() {
            break;
        }

        let init_response = session
            .get_outgoing_message()
            .map_err(|e| Error::new_session_error(e, "failed to get init response"))?
            .ok_or_else(|| Error::new_channel_error("no init response provided"))?;

        transport
            .send(init_response)
            .await
            .map_err(|e| Error::new_transport_error(e, "failed to send outgoing init response"))?;
    }

    Ok(OakSessionChannel::create(Box::new(transport), Box::new(session)))
}

// The following items are convenience traits to aid in the readability of the
// above items.

trait IntoSessionResult<T, TE> {
    fn into_session_result(self, msg: impl Into<String>) -> Result<T, TE>;
}

impl<T, TE: std::fmt::Debug> IntoSessionResult<T, TE> for anyhow::Result<T> {
    fn into_session_result(self, msg: impl Into<String>) -> Result<T, TE> {
        self.map_err(|e| Error::new_session_error(e, msg))
    }
}

trait IntoTransportResult<T, TE> {
    fn into_transport_result(self, msg: impl Into<String>) -> Result<T, TE>;
}

impl<T, TE: std::fmt::Debug> IntoTransportResult<T, TE> for result::Result<T, TE> {
    fn into_transport_result(self, msg: impl Into<String>) -> Result<T, TE> {
        self.map_err(|e| Error::new_transport_error(e, msg))
    }
}

trait ExpectNonEmpty<T, TE> {
    fn expect_non_empty(self, msg: impl Into<String>) -> Result<T, TE>;
}

impl<T, TE: std::fmt::Debug> ExpectNonEmpty<T, TE> for Option<T> {
    fn expect_non_empty(self, msg: impl Into<String>) -> Result<T, TE> {
        self.ok_or_else(|| Error::new_channel_error(msg))
    }
}
