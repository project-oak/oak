// Copyright 2017-2019 int08h LLC
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

//!
//! An implementation of the [Roughtime](https://roughtime.googlesource.com/roughtime)
//! secure time synchronization protocol.
//!
//! Roughtime aims to achieve rough time synchronisation in a secure way that doesn't
//! depend on any particular time server, and in such a way that, if a time server does
//! misbehave, clients end up with cryptographic proof of it.
//!
//! # Protocol
//!
//! Roughtime messages are represented by [`RtMessage`](struct.RtMessage.html) which
//! implements the mapping of Roughtime `u32` [`tags`](enum.Tag.html) to byte-strings.
//!
//! # Keys and Signing
//!
//! Roughtime uses an [Ed25519](https://ed25519.cr.yp.to/) key pair as the server's
//! long-term identity and a second key pair (signed by the long-term key) as a
//! delegated on-line (ephemeral) key.
//!
//! [`LongTermKey`](key/struct.LongTermKey.html) and [`OnlineKey`](key/struct.OnlineKey.html)
//! implement these elements of the protocol. The [`sign`](sign/index.html) module provides
//! signing and verification operations.
//!
//! # Client
//!
//! A Roughtime client can be found in `src/bin/client.rs`. To run the client:
//!
//! ```bash
//! $ cargo run --release --bin client roughtime.int08h.com 2002
//! ```
//!
//! Consult the client's `--help` output for all runtime options.
//!
//! # Server
//!
//! The core Roughtime server implementation is in `src/server.rs` and the server's CLI can
//! be found in `src/bin/roughenough-server.rs`.
//!
//! The server has multiple ways it can be configured,
//! see [`ServerConfig`](config/trait.ServerConfig.html) for the configuration trait and
//!
//!

#[macro_use]
extern crate log;

mod error;
mod message;
mod tag;

pub mod config;
pub mod grease;
pub mod key;
pub mod kms;
pub mod merkle;
pub mod stats;
pub mod server;
pub mod sign;

pub use crate::error::Error;
pub use crate::message::RtMessage;
pub use crate::tag::Tag;

/// Version of Roughenough
pub const VERSION: &str = "1.1.8";

/// Roughenough version string enriched with any compile-time optional features
pub fn roughenough_version() -> String {
    let kms_str = if cfg!(feature = "awskms") {
        " (+AWS KMS)"
    } else if cfg!(feature = "gcpkms") {
        " (+GCP KMS)"
    } else {
        ""
    };

    format!("{}{}", VERSION, kms_str)
}

//  Constants and magic numbers of the Roughtime protocol

/// Minimum size (in bytes) of a client request
pub const MIN_REQUEST_LENGTH: u32 = 1024;

/// Size (in bytes) of seeds used to derive private keys
pub const SEED_LENGTH: u32 = 32;

/// Size (in bytes) of an Ed25519 public key
pub const PUBKEY_LENGTH: u32 = 32;

/// Size (in bytes) of the client's nonce
pub const NONCE_LENGTH: u32 = 64;

/// Size (in bytes) of an Ed25519 signature
pub const SIGNATURE_LENGTH: u32 = 64;

/// Size (in bytes) of a SHA-512 hash
pub const HASH_LENGTH: u32 = 64;

/// Size (in bytes) of server's timestamp value
pub const TIMESTAMP_LENGTH: u32 = 8;

/// Size (in bytes) of server's time uncertainty value
pub const RADIUS_LENGTH: u32 = 4;

/// Prefixed to the server's certificate before generating or verifying certificate's signature
pub const CERTIFICATE_CONTEXT: &str = "RoughTime v1 delegation signature--\x00";

/// Prefixed to the server's response before generating or verifying the server's signature
pub const SIGNED_RESPONSE_CONTEXT: &str = "RoughTime v1 response signature\x00";

/// Value prepended to leaves prior to hashing
pub const TREE_LEAF_TWEAK: &[u8] = &[0x00];

/// Value prepended to nodes prior to hashing
pub const TREE_NODE_TWEAK: &[u8] = &[0x01];
