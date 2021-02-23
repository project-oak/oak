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
use core::borrow::Borrow;
use log::{debug, error, warn};
use oak_abi::proto::oak::application::NodeConfiguration;
use oak_io::{Decodable, Encodable};
use prost::Message;

// Re-export ABI and Services constants and structs that are also visible as part of the SDK API.
pub use oak_abi::{label::Label, ChannelReadStatus, Handle, OakStatus};

// Re-export oak_io structs that are also visible as part of the SDK API.
pub use oak_io::{
    handle::{ReadHandle, WriteHandle},
    OakError,
};

#[cfg(target_os = "macos")]
mod stubs;

pub mod crypto;
pub mod grpc;
pub mod handle;
pub mod http;
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

        pub mod crypto {
            include!(concat!(env!("OUT_DIR"), "/oak.crypto.rs"));
        }
        pub mod invocation {
            include!(concat!(env!("OUT_DIR"), "/oak.invocation.rs"));
        }
        pub mod storage {
            include!(concat!(env!("OUT_DIR"), "/oak.storage.rs"));
        }
        pub mod roughtime {
            include!(concat!(env!("OUT_DIR"), "/oak.roughtime.rs"));
        }
    }
}

/// Indicator whether an operation is executed using the Node's label-downgrading privilege or
/// without it.
#[derive(Clone, Copy, Debug)]
enum Downgrading {
    No,
    Yes,
}

// TODO(#544): re-enable relevant SDK tests

// Build a chunk of memory that is suitable for passing to oak_abi::wait_on_channels,
// holding the given collection of channel handles.
// TODO(#1854): Only accept &[&ReadHandle] once handles are always linear types
fn new_handle_space<R: Borrow<ReadHandle>>(handles: &[R]) -> Vec<u8> {
    let mut space = Vec::with_capacity(oak_abi::SPACE_BYTES_PER_HANDLE * handles.len());
    for handle in handles {
        space
            .write_u64::<byteorder::LittleEndian>(handle.borrow().handle)
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
// TODO(#1854): Only accept &[&ReadHandle] once handles are always linear types
pub fn wait_on_channels<R: Borrow<ReadHandle>>(
    handles: &[R],
) -> Result<Vec<ChannelReadStatus>, OakStatus> {
    wait_on_channels_util(handles, Downgrading::No)
}

/// The same as [`wait_on_channels`](#method.wait_on_channels), but also applies the current Node's
/// downgrade privilege when checking IFC restrictions.
// TODO(#1854): Only accept &[&ReadHandle] once handles are always linear types
pub fn wait_on_channels_with_downgrade<R: Borrow<ReadHandle>>(
    handles: &[R],
) -> Result<Vec<ChannelReadStatus>, OakStatus> {
    wait_on_channels_util(handles, Downgrading::Yes)
}

/// Helper function used by [`wait_on_channels`](#method.wait_on_channels) and
/// [`wait_on_channels_with_downgrade`](#method.wait_on_channels_with_downgrade).
// TODO(#1854): Only accept &[&ReadHandle] once handles are always linear types
fn wait_on_channels_util<R: Borrow<ReadHandle>>(
    handles: &[R],
    downgrade: Downgrading,
) -> Result<Vec<ChannelReadStatus>, OakStatus> {
    let mut space = new_handle_space(handles);
    unsafe {
        let status = match downgrade {
            Downgrading::Yes => {
                oak_abi::wait_on_channels_with_downgrade(space.as_mut_ptr(), handles.len() as u32)
            }
            Downgrading::No => oak_abi::wait_on_channels(space.as_mut_ptr(), handles.len() as u32),
        };
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
// TODO(#1854): Only accept &ReadHandle once handles are always linear types
pub fn channel_read<R: Borrow<ReadHandle>>(
    half: R,
    buf: &mut Vec<u8>,
    handles: &mut Vec<Handle>,
) -> Result<(), OakStatus> {
    channel_read_util(half.borrow(), buf, handles, Downgrading::No)
}

/// The same as [`channel_read`](#method.channel_read), but also applies the current Node's
/// downgrade privilege when checking IFC restrictions.
// TODO(#1854): Only accept &ReadHandle once handles are always linear types
pub fn channel_read_with_downgrade<R: Borrow<ReadHandle>>(
    half: R,
    buf: &mut Vec<u8>,
    handles: &mut Vec<Handle>,
) -> Result<(), OakStatus> {
    channel_read_util(half.borrow(), buf, handles, Downgrading::Yes)
}

/// Helper function used by [`channel_read`](#method.channel_read) and
/// [`channel_read_with_downgrade`](#method.channel_read_with_downgrade).
fn channel_read_util(
    half: &ReadHandle,
    buf: &mut Vec<u8>,
    handles: &mut Vec<Handle>,
    downgrade: Downgrading,
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
        let status = match downgrade {
            Downgrading::Yes => OakStatus::from_i32(unsafe {
                oak_abi::channel_read_with_downgrade(
                    half.handle,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    &mut actual_size,
                    handles_buf.as_mut_ptr(),
                    handles_buf.capacity() as u32 / 8, // Handle count, not byte count
                    &mut actual_handle_count,
                ) as i32
            }),
            Downgrading::No => OakStatus::from_i32(unsafe {
                oak_abi::channel_read(
                    half.handle,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    &mut actual_size,
                    handles_buf.as_mut_ptr(),
                    handles_buf.capacity() as u32 / 8, // Handle count, not byte count
                    &mut actual_handle_count,
                ) as i32
            }),
        };

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
// TODO(#1854): Only accept &WriteHandle once handles are always linear types
pub fn channel_write<W: Borrow<WriteHandle>>(
    half: W,
    buf: &[u8],
    handles: &[Handle],
) -> Result<(), OakStatus> {
    let handle_buf = crate::handle::pack(handles);
    let status = unsafe {
        oak_abi::channel_write(
            half.borrow().handle,
            buf.as_ptr(),
            buf.len(),
            handle_buf.as_ptr(),
            handles.len() as u32, // Number of handles, not bytes
        )
    };
    result_from_status(status as i32, ())
}

/// The same as [`channel_write`](#method.channel_write), but also applies the current Node's
/// downgrade privilege when checking IFC restrictions.
// TODO(#1854): Only accept &WriteHandle once handles are always linear types
pub fn channel_write_with_downgrade<W: Borrow<WriteHandle>>(
    half: W,
    buf: &[u8],
    handles: &[Handle],
) -> Result<(), OakStatus> {
    let handle_buf = crate::handle::pack(handles);
    let status = unsafe {
        oak_abi::channel_write_with_downgrade(
            half.borrow().handle,
            buf.as_ptr(),
            buf.len(),
            handle_buf.as_ptr(),
            handles.len() as u32, // Number of handles, not bytes
        )
    };
    result_from_status(status as i32, ())
}

/// Create a new unidirectional channel.
///
/// The provided label must be equal or more restrictive than the label of the calling node, i.e.
/// the label of the calling node must "flow to" the provided label.
///
/// On success, returns [`WriteHandle`] and a [`ReadHandle`] values for the
/// write and read halves (respectively).
pub fn channel_create(name: &str, label: &Label) -> Result<(WriteHandle, ReadHandle), OakStatus> {
    let mut write = WriteHandle {
        handle: crate::handle::invalid(),
    };
    let mut read = ReadHandle {
        handle: crate::handle::invalid(),
    };
    let label_bytes = label.serialize();
    let name_bytes = name.as_bytes();
    let status = unsafe {
        oak_abi::channel_create(
            &mut write.handle as *mut u64,
            &mut read.handle as *mut u64,
            name_bytes.as_ptr(),
            name_bytes.len(),
            label_bytes.as_ptr(),
            label_bytes.len(),
        )
    };
    result_from_status(status as i32, (write, read))
}

/// The same as [`channel_create`](#method.channel_create), but also applies the current Node's
/// downgrade privilege when checking IFC restrictions.
pub fn channel_create_with_downgrade(
    name: &str,
    label: &Label,
) -> Result<(WriteHandle, ReadHandle), OakStatus> {
    let mut write = WriteHandle {
        handle: crate::handle::invalid(),
    };
    let mut read = ReadHandle {
        handle: crate::handle::invalid(),
    };
    let label_bytes = label.serialize();
    let name_bytes = name.as_bytes();
    let status = unsafe {
        oak_abi::channel_create_with_downgrade(
            &mut write.handle as *mut u64,
            &mut read.handle as *mut u64,
            name_bytes.as_ptr(),
            name_bytes.len(),
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

/// Creates a new Node running the configuration identified by `config_name`, running the entrypoint
/// identified by `entrypoint_name` (for a Web Assembly Node; this parameter is ignored when
/// creating a pseudo-Node), with the provided `label`, and passing it the given handle.
///
/// The provided label must be equal or more restrictive than the label of the calling node, i.e.
/// the label of the calling node must "flow to" the provided label.
///
/// See https://github.com/project-oak/oak/blob/main/docs/concepts.md#labels
pub fn node_create(
    name: &str,
    config: &NodeConfiguration,
    label: &Label,
    half: ReadHandle,
) -> Result<(), OakStatus> {
    let name_bytes = name.as_bytes();
    let label_bytes = label.serialize();
    let mut config_bytes = Vec::new();
    config.encode(&mut config_bytes).map_err(|err| {
        warn!("Could not encode node configuration: {:?}", err);
        OakStatus::ErrInvalidArgs
    })?;
    let status = unsafe {
        oak_abi::node_create(
            name_bytes.as_ptr(),
            name_bytes.len(),
            config_bytes.as_ptr(),
            config_bytes.len(),
            label_bytes.as_ptr(),
            label_bytes.len(),
            half.handle,
        )
    };
    result_from_status(status as i32, ())
}

/// The same as [`node_create`](#method.node_create), but also applies the current Node's downgrade
/// privilege when checking IFC restrictions.
pub fn node_create_with_downgrade(
    name: &str,
    config: &NodeConfiguration,
    label: &Label,
    half: ReadHandle,
) -> Result<(), OakStatus> {
    let name_bytes = name.as_bytes();
    let label_bytes = label.serialize();
    let mut config_bytes = Vec::new();
    config.encode(&mut config_bytes).map_err(|err| {
        warn!("Could not encode node configuration: {:?}", err);
        OakStatus::ErrInvalidArgs
    })?;
    let status = unsafe {
        oak_abi::node_create_with_downgrade(
            name_bytes.as_ptr(),
            name_bytes.len(),
            config_bytes.as_ptr(),
            config_bytes.len(),
            label_bytes.as_ptr(),
            label_bytes.len(),
            half.handle,
        )
    };
    result_from_status(status as i32, ())
}

/// Get the [`Label`] for the channel associated with the `handle`.
pub fn channel_label_read(handle: Handle) -> Result<Label, OakStatus> {
    read_label_with(|bytes, actual_size| unsafe {
        oak_abi::channel_label_read(
            handle,
            bytes.as_mut_ptr(),
            bytes.capacity(),
            &mut *actual_size,
        ) as i32
    })
}

/// Get the [`Label`] for the current node.
pub fn node_label_read() -> Result<Label, OakStatus> {
    read_label_with(|bytes, actual_size| unsafe {
        oak_abi::node_label_read(bytes.as_mut_ptr(), bytes.capacity(), &mut *actual_size) as i32
    })
}

/// Get the downgrade privilege for the current node represented as a [`Label`].
pub fn node_privilege_read() -> Result<Label, OakStatus> {
    read_label_with(|bytes, actual_size| unsafe {
        oak_abi::node_privilege_read(bytes.as_mut_ptr(), bytes.capacity(), &mut *actual_size) as i32
    })
}

/// Helper function to read a label using `label_fetcher`.
///
/// If the buffer is too small, it will resize the buffer to the `actual_size` and try again.
fn read_label_with<F>(label_fetcher: F) -> Result<Label, OakStatus>
where
    F: Fn(&mut Vec<u8>, &mut u32) -> i32,
{
    let mut bytes = Vec::with_capacity(1024);
    for resized in &[false, true] {
        let mut actual_size: u32 = 0;
        let status = OakStatus::from_i32(label_fetcher(&mut bytes, &mut actual_size))
            .ok_or(OakStatus::ErrInternal)?;
        match status {
            OakStatus::Ok => {
                unsafe {
                    // The serialized label was successfully fetched, so set the length to the
                    // actual length.
                    bytes.set_len(actual_size as usize);
                }
                return Ok(Label::deserialize(&bytes).expect("Could not deserialize label."));
            }

            OakStatus::ErrBufferTooSmall if !(*resized) => {
                // Extend the vector to be large enough for the serialized label.
                debug!(
                    "Got space for {} bytes, need {}",
                    bytes.capacity(),
                    actual_size
                );
                bytes.reserve((actual_size as usize) - bytes.capacity());

                // Try again with a buffer resized to cope with expected size of data.
                continue;
            }

            s => {
                return Err(s);
            }
        }
    }
    error!("unreachable code reached");
    Err(OakStatus::ErrInternal)
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

/// Trait implemented by Oak Nodes (or parts thereof) that operate on commands.
///
/// It has a single method for handling commands, which are usually received via the single incoming
/// channel handle which is passed in at Node creation time, or derived from such stream.
pub trait CommandHandler {
    /// Type of the command that is handled by this instance.
    type Command;

    /// Handles a single command instance.
    ///
    /// The return value is only used for logging in case of error.
    fn handle_command(&mut self, command: Self::Command) -> anyhow::Result<()>;
}

/// Runs a command loop on the provided [`CommandHandler`]:
///
/// - waits for new messages from the provided iterator
/// - passes the typed command object to the `Node::handle_command` method of the `node`, which
///   executes a single iteration of the loop
///
/// Note the loop is only interrupted if the Node is terminated while waiting. Other errors are just
/// logged, and the loop continues with the next iteration.
pub fn run_command_loop<N: CommandHandler, R: Iterator<Item = N::Command>>(
    mut command_handler: N,
    command_iterator: R,
) {
    for command in command_iterator {
        debug!("received command");
        if let Err(err) = command_handler.handle_command(command) {
            error!("error handling command: {}", err);
        }
    }
}

/// Trait implemented by structs that correspond to entrypoint of Wasm nodes.
///
/// This statically ties together the Wasm entrypoint name (i.e. the name of the Wasm exported
/// function) and the type of messages that the node accepts with this trait.
///
/// This trait is automatically implemented for types used as part of [`entrypoint_command_handler`]
/// entrypoint definitions.
pub trait WasmEntrypoint {
    /// Name of the WebAssembly exported function that corresponds to the entrypoint of this Node.
    const ENTRYPOINT_NAME: &'static str;

    /// Type of message that the Node accepts on its inbound channel.
    type Message: Encodable + Decodable;
}

/// Trait implemented by structs that require an initialization step by receiving data over the
/// inbound channel (usually wrapped within a [`oak_io::InitWrapper`] message).
pub trait WithInit {
    type Init;

    /// Creates an instance of this struct based on the provided initialization data.
    ///
    /// Panics if there is any error.
    fn create(init: Self::Init) -> Self;
}

/// Register a new Node entrypoint.
///
/// This registers the entrypoint name and the expression that runs an event loop, and it includes
/// the static type of messages that are read from the inbound channel.
///
/// The first node of an Oak application usually receives a
/// [`ConfigMap`](oak_abi::proto::oak::application::ConfigMap) message from the Oak Runtime via the
/// initial incoming channel, which is reflected in the type of message associated with the
/// entrypoint.
///
/// ```
/// use oak::io::{Receiver, ReceiverExt};
/// use oak_abi::proto::oak::application::ConfigMap;
///
/// #[derive(Default)]
/// struct DummyNode;
///
/// impl oak::CommandHandler for DummyNode {
///     // ...
///     # type Command = oak::grpc::Invocation;
///     # fn handle_command(&mut self, command: oak::grpc::Invocation) -> anyhow::Result<()> {
///     #     unimplemented!()
///     # }
/// }
///
/// oak::entrypoint!(dummy<ConfigMap> => |receiver: Receiver<ConfigMap>| {
///     let config_map = receiver.receive().unwrap();
///     let grpc_server_listen_address = String::from_utf8(
///         config_map
///             .items
///             .get("grpc_server_listen_address")
///             .unwrap_or(&"[::]:8080".as_bytes().to_vec())
///         .to_vec()).unwrap();
///     let grpc_channel = oak::grpc::server::init(&grpc_server_listen_address)
///         .expect("could not create gRPC server pseudo-node");
///     let dispatcher = DummyNode::default();
///     oak::run_command_loop(dispatcher, grpc_channel.iter());
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
/// use oak::io::ReceiverExt;
/// use oak_abi::proto::oak::application::ConfigMap;
///
/// # fn init_all_the_things() {}
/// #
/// # #[derive(Default)]
/// # struct DummyNode;
/// #
/// # impl oak::CommandHandler for DummyNode {
/// #     type Command = oak::grpc::Invocation;
/// #     fn handle_command(&mut self, command: oak::grpc::Invocation) -> anyhow::Result<()> {
/// #         unimplemented!()
/// #     }
/// # }
/// #
/// oak::entrypoint!(its_complicated<ConfigMap> => |_receiver| {
///     init_all_the_things();
///     let dispatcher = DummyNode::default();
///     let grpc_channel = oak::grpc::server::init("[::]:8080")
///         .expect("could not create gRPC server pseudo-node");
///     oak::run_command_loop(dispatcher, grpc_channel.iter());
/// });
/// #
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! entrypoint {
    ($name:ident < $msg:ty > => $handler:expr) => {
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

                // Run the Node's entrypoint handler.
                let in_read_handle = ::oak::ReadHandle { handle: in_handle };
                let receiver = ::oak::io::Receiver::<$msg>::new(in_read_handle);
                $handler(receiver);
            });
        }
    };
}

/// Similar to [`entrypoint`], but offers a less verbose API in case in which the handler is a
/// [`CommandHandler`] instance. In this case, the type of incoming messages is inferred from the
/// generic type associated with the handler instance, and only the entrypoint name needs to be
/// specified.
///
/// The generated implementation of the body of this node sets up logging, creates an instance of
/// the handler, and then immediately calls [`run_command_loop`] on this instance.
///
/// It also automatically implements the [`WasmEntrypoint`] trait for the provided handler type
/// which reflect the entrypoint name given via the macro invocation.
///
/// ```
/// use oak_abi::proto::oak::application::ConfigMap;
///
/// #[derive(Default)]
/// struct Main;
///
/// impl oak::CommandHandler for Main {
///     type Command = ConfigMap;
///     fn handle_command(&mut self, command: ConfigMap) -> anyhow::Result<()> {
///         // ...
/// #        unimplemented!()
///     }
/// }
///
/// oak::entrypoint_command_handler!(oak_main => Main);
/// ```
#[macro_export]
macro_rules! entrypoint_command_handler {
    ($name:ident => $handler:ty) => {
        ::oak::entrypoint!($name < _ > => |receiver: ::oak::io::Receiver<_>| {
            use ::oak::io::ReceiverExt;
            let instance = <$handler>::default();
            ::oak::run_command_loop(instance, receiver.iter());
        });
        impl ::oak::WasmEntrypoint for $handler {
            const ENTRYPOINT_NAME: &'static str = std::stringify!($name);
            type Message = <$handler as ::oak::CommandHandler>::Command;
        }
    };
}

/// Similar to [`entrypoint_command_handler`], but for nodes that expect to receive initialization
/// data via an [`oak_io::InitWrapper`] instance over the inbound channel before processing
/// subsequent commands.
#[macro_export]
macro_rules! entrypoint_command_handler_init {
    ($name:ident => $handler:ty) => {
        ::oak::entrypoint!($name < _ > => |receiver: ::oak::io::Receiver<::oak_io::InitWrapper<_, _>>| {
            use ::oak::io::ReceiverExt;
            use ::oak::WithInit;
            let init_wrapper = receiver.receive().expect("could not receive init");
            receiver.close().expect("could not close the receiver channel");
            let instance = <$handler>::create(init_wrapper.init);
            ::oak::run_command_loop(instance, init_wrapper.command_receiver.iter());
        });
        impl ::oak::WasmEntrypoint for $handler {
            const ENTRYPOINT_NAME: &'static str = std::stringify!($name);
            type Message = ::oak_io::InitWrapper<<$handler as ::oak::WithInit>::Init, <$handler as ::oak::CommandHandler>::Command>;
        }
    };
}
