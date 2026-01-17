//
// Copyright 2024 The Project Oak Authors
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

#[macro_use]
extern crate alloc;

#[cfg(test)]
extern crate std;

pub mod aggregators;
pub mod attestation;
pub mod channel;
pub mod config;
pub mod encryptors;
pub mod generator;
pub mod handshake;
pub mod key_extractor;
pub mod session;
pub mod session_binding;
pub mod verifier;

pub use session::{ClientSession, ServerSession, Session};

/// Trait that represents a state-machine for protocol message generation.
/// Incoming and outgoing messages are represented as associated types`Input`
/// and `Output`.
///
/// This trait can be used to implement bidirectional streams, meaning that
/// there doesn't have to be a one-to-one correspondence between incoming and
/// outgoing messages.
///
/// If one of the methods returns an error, it means that there was a protocol
/// error and the session needs to be restarted (because the state-machine is in
/// an incorrect state).
pub trait ProtocolEngine {
    type Input;
    type Output;
    /// Puts a message received from the peer into the state-machine changing
    /// its state.
    ///
    /// Method returns `Result<Option<()>>` with the corresponding outcomes:
    /// - `Ok(None)`: No incoming messages were expected
    /// - `Ok(Some(()))`: An incoming message was accepted by the state-machine
    /// - `Err`: Protocol error
    fn put_incoming_message(&mut self, incoming_message: Self::Input)
    -> anyhow::Result<Option<()>>;

    /// Creates a next message that needs to be sent to the peer.
    ///
    /// Method returns `Result<Option<()>>` with the corresponding outcomes:
    /// - `Ok(None)`: No outgoing messages
    /// - `Ok(Some(O))`: An outgoing message that needs to be sent to the peer
    /// - `Err`: Protocol error
    fn get_outgoing_message(&mut self) -> anyhow::Result<Option<Self::Output>>;
}
