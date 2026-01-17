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

use alloc::vec::Vec;

use anyhow::Context;
use oak_proto_rust::oak::session::v1::PlaintextMessage;

use crate::{ProtocolEngine, session::Session};

/// A convenience implementation for encryption/decryption for a session.
///
/// Note that using the trait doesn't prevent you from trying to use the methods
/// with a session in the wrong state (i.e., the session is not "open").
///
/// This convenience trait only works with an ordered transport. If the
/// underlying message transport may deliver messages out of order, then you
/// will need to use the lower-level abstractions provided by [`Session`] and
/// [`ProtocolEngine`].
///
/// If you are using this trait, you should avoid using the lower-level API,
/// unless you really know what you're doing.
///
/// You can use [`SessionInitializer`] to help manage the initialization
/// sequence needed to open the session.
pub trait SessionChannel: ProtocolEngine + Session {
    fn encrypt(
        &mut self,
        plaintext: impl Into<Vec<u8>>,
    ) -> anyhow::Result<<Self as ProtocolEngine>::Output> {
        anyhow::ensure!(self.is_open(), "Session is not open");
        self.write(PlaintextMessage { plaintext: plaintext.into() })
            .context("writing message for encryption")?;
        self.get_outgoing_message()
            .context("getting outgoing message")?
            .context("(Library Error, please report) unexpectedly empty outgoing message")
    }

    fn decrypt(
        &mut self,
        incoming_message: <Self as ProtocolEngine>::Input,
    ) -> anyhow::Result<Vec<u8>> {
        anyhow::ensure!(self.is_open(), "Session is not open");
        self.put_incoming_message(incoming_message).context("putting incoming message")?;
        Ok(self
            .read()
            .context("reading decrypted message")?
            .context("(Library Error, please report) unexpectedly empty decrypted message")?
            .plaintext)
    }
}

impl<S: ProtocolEngine + Session> SessionChannel for S {}
/// A trait that helps to implement the initialization logic for an Oak Session.
///
/// This abstraction is designed to be simple to use, but flexible enough for
/// different implementation patterns. It provides only synchronous methods,
/// along with additional helper methods to adapt its usage to common patterns
/// in Rust.
///
/// To use it for a client in a synchronous loop:
/// ```
/// use oak_session::channel::SessionInitializer;
///
/// while !client_session.is_open() {
///     let request = client_session.next_init_message()?;
///     send_to_server(request)?;
///     if !client_session.is_open() {
///         let init_response = read_from_server()?;
///         client_session.handle_init_message(init_response)?;
///     }
/// }
/// ```
///
/// And for a server in a synchronous loop:
/// ```
/// use oak_session::channel::SessionInitializer;
///
/// while !server_session.is_open() {
///     let request = read_from_client()?;
///     server_session.handle_init_message(request)?;
///     if !server_session.is_open() {
///         let response = server_session.next_init_message()?;
///         send_to_client(response)?;
///     }
/// }
/// ```
pub trait SessionInitializer: ProtocolEngine + Session {
    fn next_init_message(&mut self) -> anyhow::Result<<Self as ProtocolEngine>::Output> {
        anyhow::ensure!(!self.is_open(), "Session already open");
        self.get_outgoing_message()
            .context("getting next outgoing message")?
            .context("unexpected empty first init message")
    }

    fn handle_init_message(
        &mut self,
        response: <Self as ProtocolEngine>::Input,
    ) -> anyhow::Result<()> {
        anyhow::ensure!(!self.is_open(), "Session already open");
        self.put_incoming_message(response).context("putting incoming message")?;
        Ok(())
    }
}

impl<S: ProtocolEngine + Session> SessionInitializer for S {}
