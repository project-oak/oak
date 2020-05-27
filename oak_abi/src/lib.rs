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

//! Type, constant and Wasm host function definitions for the Oak application
//! binary interface (ABI).

pub mod grpc;
pub mod label;
pub mod proto;

pub use proto::oak::{ChannelReadStatus, OakStatus};

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

// The Oak ABI primarily consists of a collection of Wasm host functions in the
// "oak" module that are made available to WebAssembly Nodes running under the
// Oak runtime.
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
    /// [`ErrBufferTooSmall`] or [`ErrHandleSpaceTooSmall`] will be
    /// returned.  In either case, the required sizes will be returned in the
    /// spaces provided by `actual_size` and `actual_handle_count`.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    /// If no message is available on the channel, [`ErrChannelEmpty`] will be
    /// returned.
    ///
    /// [`ErrBufferTooSmall`]: crate::OakStatus::ErrBufferTooSmall
    /// [`ErrChannelEmpty`]: crate::OakStatus::ErrChannelEmpty
    /// [`ErrHandleSpaceTooSmall`]: crate::OakStatus::ErrHandleSpaceTooSmall
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

    /// Create a new unidirectional Channel.
    ///
    /// Returns handles for the the write and read halves of the Channel in the spaces given by
    /// `write` and `read`.
    ///
    /// The label to assign to the newly created Channel is provided in the memory area given by
    /// `label_buf` and `label_len`.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// [`OakStatus`]: crate::OakStatus
    pub fn channel_create(
        write: *mut u64,
        read: *mut u64,
        label_buf: *const u8,
        label_len: usize,
    ) -> u32;

    /// Closes the channel identified by `handle`.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// [`OakStatus`]: crate::OakStatus
    pub fn channel_close(handle: u64) -> u32;

    /// Creates a new Node instance running code identified by a serialized [`NodeConfiguration`].
    ///
    /// The serialized configuration object is provided in the memory area given by `config_buf` and
    /// `config_len`.
    ///
    /// The label to assign to the newly created Node is provided in the memory area given by
    /// `label_buf` and `label_len`.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// [`OakStatus`]: crate::OakStatus
    /// [`NodeConfiguration`]: crate::proto::oak::application::NodeConfiguration
    pub fn node_create(
        config_buf: *const u8,
        config_len: usize,
        label_buf: *const u8,
        label_len: usize,
        handle: u64,
    ) -> u32;

    /// Fill a buffer with random data.
    ///
    /// Returns the status of the operation, as an [`OakStatus`] value.
    ///
    /// [`OakStatus`]: crate::OakStatus
    pub fn random_get(buf: *mut u8, len: usize) -> u32;
}
