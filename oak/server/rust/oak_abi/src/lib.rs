//
// Copyright 2019 The Project Oak Authors
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

//! Type, constant and Wasm host function definitions for the Oak application binary interface.

// TODO(#638): Generate from protobuf in a no_std compatible way
#[cfg(feature = "std")]
pub use proto::oak_api::ChannelReadStatus;
#[cfg(feature = "std")]
pub use proto::oak_api::OakStatus;

#[cfg(feature = "std")]
pub mod proto;

// TODO(#638): Generate from protobuf in a no_std compatible way
#[cfg(feature = "no_std")]
pub mod proto {
    #![allow(dead_code)]
    #![allow(missing_docs)]
    #![allow(non_camel_case_types)]
    #![allow(non_snake_case)]
    #![allow(non_upper_case_globals)]

    #[derive(Clone, PartialEq, Eq, Debug, Hash)]
    pub enum OakStatus {
        OAK_STATUS_UNSPECIFIED = 0,
        OK = 1,
        ERR_BAD_HANDLE = 2,
        ERR_INVALID_ARGS = 3,
        ERR_CHANNEL_CLOSED = 4,
        ERR_BUFFER_TOO_SMALL = 5,
        ERR_HANDLE_SPACE_TOO_SMALL = 6,
        ERR_OUT_OF_RANGE = 7,
        ERR_INTERNAL = 8,
        ERR_TERMINATED = 9,
        ERR_CHANNEL_EMPTY = 10,
    }

    #[derive(Clone, PartialEq, Eq, Debug, Hash)]
    pub enum ChannelReadStatus {
        NOT_READY = 0,
        READ_READY = 1,
        INVALID_CHANNEL = 2,
        ORPHANED = 3,
    }
}

#[cfg(feature = "no_std")]
pub use proto::{ChannelReadStatus, OakStatus};

/// Handle used to identify read or write channel halves.
///
/// These handles are used for all host function calls.
pub type Handle = u64;

/// Expected type for a Node entrypoint that is exposed as a Wasm export.
pub type NodeMainC = extern "C" fn(Handle);

/// Expected Rust type for a Node entrypoint.
pub type NodeMain = fn(Handle);

/// Number of bytes needed per-handle for channel readiness notifications.
///
/// The notification space consists of the channel handle (as a little-endian
/// u64) followed by a single byte indicating the channel readiness, as
/// a `ChannelReadStatus` value.
pub const SPACE_BYTES_PER_HANDLE: usize = 9;

/// Invalid handle value.
pub const INVALID_HANDLE: Handle = 0;

// See https://rustwasm.github.io/book/reference/js-ffi.html
#[link(wasm_import_module = "oak")]
extern "C" {
    /// Wait for channels to be ready for reading.
    ///
    /// Blocks until data is available for reading from one of the specified
    /// channel handles.  The channel handles are encoded in a buffer `buf` that
    /// holds `count` contiguous chunks of size [`SPACE_BYTES_PER_HANDLE`].
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// [`OakStatus`]: crate::OakStatus
    pub fn wait_on_channels(buf: *mut u8, count: u32) -> u32;

    /// Read a message from a channel.
    ///
    /// Reads from the channel identified by `handle`, storing data into `buf`
    /// and associated channel handles into `handle_buf`.  The size of the
    /// returned data is indicated by `actual_size`, and the count of returned
    /// channel handles is indicated by `actual_handle_count`.
    ///
    /// If the provided spaces for data (`buf` plus `size`) or handles
    /// (`handle_buf` plus 8 x `handle_count`) are not large enough for the read
    /// operation, then no data will be returned and either
    /// [`ERR_BUFFER_TOO_SMALL`] or [`ERR_HANDLE_SPACE_TOO_SMALL`] will be
    /// returned.  In either case, the required sizes will be returned in the
    /// spaces provided by `actual_size` and `actual_handle_count`.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    /// If no message is available on the channel, [`ERR_CHANNEL_EMPTY`] will be
    /// returned.
    ///
    /// [`ERR_BUFFER_TOO_SMALL`]: crate::OakStatus::ERR_BUFFER_TOO_SMALL
    /// [`ERR_CHANNEL_EMPTY`]: crate::OakStatus::ERR_CHANNEL_EMPTY
    /// [`ERR_HANDLE_SPACE_TOO_SMALL`]: crate::OakStatus::ERR_HANDLE_SPACE_TOO_SMALL
    /// [`OakStatus`]: crate::OakStatus
    pub fn channel_read(
        handle: u64,
        buf: *mut u8,
        size: usize,
        actual_size: *mut u32,
        handle_buf: *mut u8,
        handle_count: u32,
        actual_handle_count: *mut u32,
    ) -> u32;

    /// Write a message to a channel.
    ///
    /// Write `size` bytes of data from `buf`, together with `handle_count` handles from
    /// the space at `handle_buf`, to the channel identified by `handle`.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// [`OakStatus`]: crate::OakStatus
    pub fn channel_write(
        handle: u64,
        buf: *const u8,
        size: usize,
        handle_buf: *const u8,
        handle_count: u32,
    ) -> u32;

    /// Create a new unidirectional channel.
    ///
    /// Returns handles for the the write and read halves of the channel in
    /// the spaces given by `write` and `read`.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// [`OakStatus`]: crate::OakStatus
    pub fn channel_create(write: *mut u64, read: *mut u64) -> u32;

    /// Close a channel.
    ///
    /// Close the channel identified by `handle`.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// [`OakStatus`]: crate::OakStatus
    pub fn channel_close(handle: u64) -> u32;

    /// Create a new Node instance running code identified by configuration
    /// name and entrypoint.
    ///
    /// The configuration name is provided in the memory area given by
    /// `config_buf` and `config_len`; the entrypoint name is provided in the
    /// memory area given by `entrypoint_buf` and `entrypoint_len`.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// [`OakStatus`]: crate::OakStatus
    pub fn node_create(
        config_buf: *const u8,
        config_len: usize,
        entrypoint_buf: *const u8,
        entrypoint_len: usize,
        handle: u64,
    ) -> u32;

    /// Fill a buffer with random data.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// [`OakStatus`]: crate::OakStatus
    pub fn random_get(buf: *mut u8, len: usize) -> u32;
}
