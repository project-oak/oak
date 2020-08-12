//
// Copyright 2018 The Project Oak Authors
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

//! SDK functionality that provides idiomatic Rust wrappers around the
//! underlying Oak platform functionality.

use byteorder::WriteBytesExt;
use io::ReceiverExt;
use log::{debug, error, info, trace, warn};
use oak_abi::proto::oak::application::{ConfigMap, NodeConfiguration};
use prost::Message;

// Re-export ABI constants that are also visible as part of the SDK API.
pub use oak_abi::{label::Label, ChannelReadStatus, Handle, OakStatus};

// Re-export oak_io structs that are also visible as part of the SDK API.
pub use oak_io::handle::{ReadHandle, WriteHandle};

mod error;
#[cfg(target_os = "macos")]
mod stubs;
pub use error::OakError;

pub mod grpc;
pub mod handle;
pub mod http;
pub mod invocations;
pub mod io;
pub mod logger;
pub mod node_config;
pub mod rand;
pub mod roughtime;
pub mod storage;

pub mod proto {
    //! Auto-generated code derived from protocol buffer definitions.
    pub mod oak {
        // The storage protobuf messages use the label.Label type which is built
        // in the `oak_abi` crate, so make it available here too.
        pub use oak_abi::proto::oak::{application, label};
        pub mod storage {
            include!(concat!(env!("OUT_DIR"), "/oak.storage.rs"));
        }
        pub mod roughtime {
            include!(concat!(env!("OUT_DIR"), "/oak.roughtime.rs"));
        }
    }
}

// TODO(#544): re-enable relevant SDK tests

// Build a chunk of memory that is suitable for passing to oak_abi::wait_on_channels,
// holding the given collection of channel handles.
fn new_handle_space(handles: &[ReadHandle]) -> Vec<u8> {
    let mut space = Vec::with_capacity(oak_abi::SPACE_BYTES_PER_HANDLE * handles.len());
    for handle in handles {
        space
            .write_u64::<byteorder::LittleEndian>(handle.handle)
            .unwrap();
        space.push(0x00);
    }
    space
}

// Prepare a handle space for polling by clearing all of the message-pending
// indicator bytes.
fn prep_handle_space(space: &mut [u8]) {
    let count = space.len() / 8;
    for i in 0..count {
        space[i * oak_abi::SPACE_BYTES_PER_HANDLE + (oak_abi::SPACE_BYTES_PER_HANDLE - 1)] = 0;
    }
}

/// Wait for one or more of the provided handles to become ready for reading
/// from.  On success, the returned vector of [`ChannelReadStatus`] values
/// will be in 1-1 correspondence with the passed-in vector of [`Handle`]s.
///
/// This is a convenience wrapper around the [`oak_abi::wait_on_channels`] host
/// function. This version is easier to use in Rust but is less efficient
/// (because the notification space is re-created on each invocation).
pub fn wait_on_channels(handles: &[ReadHandle]) -> Result<Vec<ChannelReadStatus>, OakStatus> {
    let mut space = new_handle_space(handles);
    unsafe {
        let status = oak_abi::wait_on_channels(space.as_mut_ptr(), handles.len() as u32);
        result_from_status(status as i32, ())?;
        let mut results = Vec::with_capacity(handles.len());
        for i in 0..handles.len() {
            match space
                .get(i * oak_abi::SPACE_BYTES_PER_HANDLE + (oak_abi::SPACE_BYTES_PER_HANDLE - 1))
                .cloned()
                .map(i32::from)
                .and_then(ChannelReadStatus::from_i32)
            {
                Some(status) => results.push(status),
                None => return Err(OakStatus::Unspecified),
            }
        }
        Ok(results)
    }
}

/// Read a message from a channel without blocking.
///
/// It also returns an error if the underlying channel is empty (i.e. not ready to read).
///
/// The provided vectors for received data and associated handles will be
/// resized to accommodate the information in the message; any data already
/// held in the vectors will be overwritten.
pub fn channel_read(
    half: ReadHandle,
    buf: &mut Vec<u8>,
    handles: &mut Vec<Handle>,
) -> Result<(), OakStatus> {
    // Try reading from the channel twice: first with provided vectors, making
    // use of their available capacity, then with vectors whose capacity has
    // been extended to meet size requirements.

    // We cannot deserialize directly into the handles vector because `Handle`
    // may not have the correct memory layout, so create a separate buffer with
    // equivalent capacity.
    let mut handles_buf = Vec::with_capacity(handles.capacity() * 8);
    for resized in &[false, true] {
        let mut actual_size: u32 = 0;
        let mut actual_handle_count: u32 = 0;
        let status = OakStatus::from_i32(unsafe {
            oak_abi::channel_read(
                half.handle,
                buf.as_mut_ptr(),
                buf.capacity(),
                &mut actual_size,
                handles_buf.as_mut_ptr(),
                handles_buf.capacity() as u32 / 8, // Handle count, not byte count
                &mut actual_handle_count,
            ) as i32
        });

        match status {
            Some(s) => match s {
                OakStatus::Ok | OakStatus::ErrChannelEmpty => {
                    unsafe {
                        // The read operation succeeded, and overwrote some fraction
                        // of the vectors' available capacity with returned data (possibly
                        // zero).  As the data is already present in the vectors, set
                        // their length to match what's available.
                        buf.set_len(actual_size as usize);
                        // actual_handle_count is number of handles not bytes
                        handles_buf.set_len(actual_handle_count as usize * 8);
                    }
                    crate::handle::unpack(&handles_buf, actual_handle_count, handles);
                    if s == OakStatus::Ok {
                        return Ok(());
                    } else {
                        return Err(s);
                    }
                }

                OakStatus::ErrBufferTooSmall | OakStatus::ErrHandleSpaceTooSmall if !(*resized) => {
                    // Extend the vectors to be large enough for the message
                    debug!(
                        "Got space for {} bytes, need {}",
                        buf.capacity(),
                        actual_size
                    );
                    if (actual_size as usize) > buf.capacity() {
                        let extra = (actual_size as usize) - buf.len();
                        buf.reserve(extra);
                    }

                    let handles_capacity = handles_buf.capacity() / 8;
                    debug!(
                        "Got space for {} handles, need {}",
                        handles_capacity, actual_handle_count
                    );
                    if (actual_handle_count as usize) > handles_capacity {
                        let extra = (actual_handle_count as usize * 8) - handles_buf.len();
                        handles_buf.reserve(extra);
                    }

                    // Try again with a buffer resized to cope with expected size of data.
                    continue;
                }

                s => {
                    return Err(s);
                }
            },
            None => {
                return Err(OakStatus::ErrInternal);
            }
        }
    }
    error!("unreachable code reached");
    Err(OakStatus::ErrInternal)
}

/// Write a message to a channel.
pub fn channel_write(half: WriteHandle, buf: &[u8], handles: &[Handle]) -> Result<(), OakStatus> {
    let handle_buf = crate::handle::pack(handles);
    let status = unsafe {
        oak_abi::channel_write(
            half.handle,
            buf.as_ptr(),
            buf.len(),
            handle_buf.as_ptr(),
            handles.len() as u32, // Number of handles, not bytes
        )
    };
    result_from_status(status as i32, ())
}

/// Similar to [`channel_create_with_label`], but with a fixed label corresponding to "public
/// untrusted".
pub fn channel_create() -> Result<(WriteHandle, ReadHandle), OakStatus> {
    channel_create_with_label(&Label::public_untrusted())
}

/// Create a new unidirectional channel.
///
/// The provided label must be equal or more restrictive than the label of the calling node, i.e.
/// the label of the calling node must "flow to" the provided label.
///
/// On success, returns [`WriteHandle`] and a [`ReadHandle`] values for the
/// write and read halves (respectively).
pub fn channel_create_with_label(label: &Label) -> Result<(WriteHandle, ReadHandle), OakStatus> {
    let mut write = WriteHandle {
        handle: crate::handle::invalid(),
    };
    let mut read = ReadHandle {
        handle: crate::handle::invalid(),
    };
    let label_bytes = label.serialize();
    let status = unsafe {
        oak_abi::channel_create(
            &mut write.handle as *mut u64,
            &mut read.handle as *mut u64,
            label_bytes.as_ptr(),
            label_bytes.len(),
        )
    };
    result_from_status(status as i32, (write, read))
}

/// Close the specified channel [`Handle`].
pub fn channel_close(handle: Handle) -> Result<(), OakStatus> {
    let status = unsafe { oak_abi::channel_close(handle) };
    result_from_status(status as i32, ())
}

/// Similar to [`node_create_with_label`], but with a fixed label corresponding to "public
/// untrusted".
pub fn node_create(config: &NodeConfiguration, half: ReadHandle) -> Result<(), OakStatus> {
    node_create_with_label(config, &Label::public_untrusted(), half)
}

/// Creates a new Node running the configuration identified by `config_name`, running the entrypoint
/// identified by `entrypoint_name` (for a Web Assembly Node; this parameter is ignored when
/// creating a pseudo-Node), with the provided `label`, and passing it the given handle.
///
/// The provided label must be equal or more restrictive than the label of the calling node, i.e.
/// the label of the calling node must "flow to" the provided label.
///
/// See https://github.com/project-oak/oak/blob/main/docs/concepts.md#labels
pub fn node_create_with_label(
    config: &NodeConfiguration,
    label: &Label,
    half: ReadHandle,
) -> Result<(), OakStatus> {
    let label_bytes = label.serialize();
    let mut config_bytes = Vec::new();
    config.encode(&mut config_bytes).map_err(|err| {
        warn!("Could not encode node configuration: {:?}", err);
        OakStatus::ErrInvalidArgs
    })?;
    let status = unsafe {
        oak_abi::node_create(
            config_bytes.as_ptr(),
            config_bytes.len(),
            label_bytes.as_ptr(),
            label_bytes.len(),
            half.handle,
        )
    };
    result_from_status(status as i32, ())
}

/// Fill a buffer with random data.
pub fn random_get(buf: &mut [u8]) -> Result<(), OakStatus> {
    let status = unsafe { oak_abi::random_get(buf.as_mut_ptr(), buf.len()) };
    result_from_status(status as i32, ())
}

/// Convert a status returned from a host function call to a `Result`.
///
/// The status is interpreted as an int representing an `OakStatus` enum value.
///
/// If the status is `OK` then return the provided value as `Result::Ok`, otherwise return the
/// status as `Result::Err`.
///
/// Note that host function calls usually return an `u32` because of limitations of the Wasm type
/// system, so these values would usually be converted (via a cast) to `i32` by callers.
pub fn result_from_status<T>(status: i32, val: T) -> Result<T, OakStatus> {
    match OakStatus::from_i32(status) {
        Some(OakStatus::Ok) => Ok(val),
        Some(status) => Err(status),
        None => Err(OakStatus::Unspecified),
    }
}

/// Install a panic hook that logs [panic information].
///
/// Logs panic infomation to the logging channel, if one is set.
///
/// [panic information]: std::panic::PanicInfo
pub fn set_panic_hook() {
    std::panic::set_hook(Box::new(|panic_info| {
        let payload = panic_info.payload();
        // The payload can be a static string slice or a string, depending on how panic was called.
        // Code for extracting the message is inspired by the rust default panic hook:
        // https://github.com/rust-lang/rust/blob/master/src/libstd/panicking.rs#L188-L194
        let msg = match payload.downcast_ref::<&'static str>() {
            Some(content) => *content,
            None => match payload.downcast_ref::<String>() {
                Some(content) => content.as_ref(),
                None => "<UNKNOWN MESSAGE>",
            },
        };
        let (file, line) = match panic_info.location() {
            Some(location) => (location.file(), location.line()),
            None => ("<UNKNOWN FILE>", 0),
        };
        error!(
            "panic occurred in file '{}' at line {}: {}",
            file, line, msg
        );
    }));
}

/// Trait implemented by Oak Nodes that operate on commands.
///
/// It has a single method for handling commands, which are [`Decodable`](crate::io::Decodable)
/// objects that are received via the single incoming channel handle which is passed in at Node
/// creation time. The return value is only used for logging in case of failure.
pub trait Node<T: crate::io::Decodable> {
    fn handle_command(&mut self, command: T) -> Result<(), crate::OakError>;
}

/// Retrieve the Application's `ConfigMap` from the read handle for the start-of-day
/// initial channel.
pub fn app_config_map(initial_handle: ReadHandle) -> Result<ConfigMap, OakError> {
    let receiver = crate::io::Receiver::new(initial_handle);
    let result = receiver.receive();
    if let Err(err) = receiver.close() {
        error!("Failed to close initial channel: {:?}", err);
    }
    result
}

/// Run an event loop on the provided `node`:
///
/// - wait for new messages on the provided channel `in_channel`
/// - if the runtime signals that the Node was terminated while waiting, then exit the event loop
/// - otherwise, read the available message via the provided channel handle
/// - decode the message from (bytes + handles) to the specified type `T`
/// - pass the typed object to the `Node::handle_command` method of the `node`, which executes a
///   single iteration of the event loop
///
/// Note the loop is only interrupted if the Node is terminated while waiting. Other errors are just
/// logged, and the event loop continues with the next iteration.

pub fn run_event_loop<T: crate::io::Decodable, N: Node<T>>(
    mut node: N,
    receiver: crate::io::Receiver<T>,
) {
    if !crate::handle::is_valid(receiver.handle.handle) {
        error!("{:?}: invalid input handle", receiver);
        return;
    }
    info!("{:?}: starting event loop", receiver);
    loop {
        // First wait until a message is available. If the Node was terminated while waiting, this
        // will return `ErrTerminated`, which indicates that the event loop should be terminated.
        // For any other error raised while waiting is logged, we try and determine whether it is
        // transient or not, and then continue or terminate the event loop, respectively.
        match receiver.wait() {
            Err(status) => {
                use crate::OakStatus::*;
                match status {
                    ErrTerminated => {
                        info!(
                            "{:?}: received termination status: {:?}; terminating event loop",
                            receiver, status
                        );
                        return;
                    }
                    _ => {
                        error!(
                            "{:?}: received status: {:?}; but `Receiver::wait` never returns an error other than `ErrTerminated`",
                            receiver, status
                        );
                        return;
                    }
                }
            }
            Ok(status) => match status {
                ChannelReadStatus::ReadReady => trace!("{:?}: wait over", receiver),
                ChannelReadStatus::Orphaned
                | ChannelReadStatus::PermissionDenied
                | ChannelReadStatus::InvalidChannel => {
                    warn!(
                        "{:?}: received invalid channel read status: {:?}; terminating event loop",
                        receiver, status
                    );
                    return;
                }
                ChannelReadStatus::NotReady => {
                    error!(
                        "{:?}: received `ChannelReadStatus::NotReady`, which should never be returned from `Receiver::wait`.",
                        receiver);
                    return;
                }
            },
        }
        match receiver.try_receive() {
            Ok(command) => {
                info!("{:?}: received command", receiver);
                if let Err(err) = node.handle_command(command) {
                    error!("{:?}: error handling command: {}", receiver, err);
                }
            }
            Err(err) => {
                error!("{:?}: error receiving command: {}", receiver, err);
            }
        }
    }
}

/// Register a new Node entrypoint.
///
/// This registers the entrypoint name and the expression that runs an event loop.
///
/// ```
/// #[derive(Default)]
/// struct DummyNode;
///
/// impl oak::Node<oak::grpc::Invocation> for DummyNode {
///     // ...
///     # fn handle_command(&mut self, command: oak::grpc::Invocation) -> Result<(), oak::OakError> {
///     #     unimplemented!()
///     # }
/// }
///
/// oak::entrypoint!(dummy => |_in_channel| {
///     let dispatcher = DummyNode::default();
///     let grpc_channel = oak::grpc::server::init("[::]:8080")
///         .expect("could not create gRPC server pseudo-node");
///     oak::run_event_loop(dispatcher, grpc_channel);
/// });
///
/// # fn main() {}
/// ```
///
/// Entrypoints need to be declared in the global scope (as opposed to for example
/// in a function body). Is recommended but not required to define all entrypoints of your
/// module in `lib.rs`.
///
/// If instantiating your Node requires some setup, it is possible to do that in the Node
/// expression too:
///
/// ```
/// # fn init_all_the_things() {}
/// #
/// # #[derive(Default)]
/// # struct DummyNode;
/// #
/// # impl oak::Node<oak::grpc::Invocation> for DummyNode {
/// #     fn handle_command(&mut self, command: oak::grpc::Invocation) -> Result<(), oak::OakError> {
/// #         unimplemented!()
/// #     }
/// # }
/// #
/// oak::entrypoint!(its_complicated => |_in_channel| {
///     init_all_the_things();
///     let dispatcher = DummyNode::default();
///     let grpc_channel = oak::grpc::server::init("[::]:8080")
///         .expect("could not create gRPC server pseudo-node");
///     oak::run_event_loop(dispatcher, grpc_channel);
/// });
/// #
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! entrypoint {
    ($name:ident => $main_function:expr) => {
        // Do not mangle these functions when running unit tests, because the Rust unit test
        // framework will add a `pub extern "C" fn main()` containing the test runner. This can
        // cause clashes when $name = main. We don't fully omit it in tests so that compile errors
        // in the Node creation expression are still caught, and unit tests can still refer to the
        // symbol if they really want to.
        #[cfg_attr(not(test), no_mangle)]
        pub extern "C" fn $name(in_handle: u64) {
            // A panic in the Rust module code cannot safely pass through the FFI
            // boundary, so catch any panics here and drop them.
            // https://doc.rust-lang.org/nomicon/ffi.html#ffi-and-panics
            let _ = ::std::panic::catch_unwind(|| {
                ::oak::set_panic_hook();

                // Run the Node's `main` function.
                let in_channel = ::oak::ReadHandle { handle: in_handle };
                $main_function(in_channel);
            });
        }
    };
}
