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

//! Test utilities to help with unit testing of Oak SDK code.

use lazy_static::lazy_static;
use log::{debug, info, warn};

use byteorder::{ReadBytesExt, WriteBytesExt};
use oak::OakStatus;
use oak_abi::{Handle, NodeMain};
pub use oak_runtime::WasmEntrypointFullName;
use oak_runtime::{proto, OakMessage, OakRuntime};
use protobuf::{Message, ProtobufEnum};
use rand::Rng;
use std::cell::RefCell;
use std::collections::hash_map::RandomState;
use std::collections::HashMap;
use std::convert::TryInto;
use std::io::Cursor;
use std::sync::{Once, RwLock};
use std::thread::spawn;

// Node name used for single-Node tests.
pub static DEFAULT_NODE_NAME: &str = "internal-0";

// Test-only mock runtime which is used to service any calls to TCB functionality.
// This is a mutable global (!) because the code under test expects to find
// global entrypoints corresponding to the Oak TCB, and there's no other way to
// get at the relevant associated state.
lazy_static! {
    static ref RUNTIME: RwLock<OakRuntime> = RwLock::new(OakRuntime::new(Some(DEFAULT_NODE_NAME)));
}

const RUNTIME_MISSING: &str = "global OakRuntime object missing";

// Per-thread Node name.
thread_local! {
    static NODE_NAME: RefCell<String> = RefCell::new(DEFAULT_NODE_NAME.to_string());
}

// Return a copy of the node name associated with the current thread.
fn node_name() -> String {
    NODE_NAME.with(|node_name| node_name.borrow().clone())
}

// Set the node name for the current thread.
fn set_node_name(name: String) {
    NODE_NAME.with(|node_name| node_name.replace(name));
}

// Implementations of the Oak API host functions in Rust for testing.
// These implementations generally handle the unsafe raw memory manipulation
// then forward on to the equivalent method on the current OakRuntime instance.

/// Test implementation of channel wait functionality.
///
/// # Safety
///
/// The linear memory range [buf, buf+count*SPACE_BYTES_PER_HANDLE) must be
/// valid.
#[no_mangle]
pub unsafe extern "C" fn wait_on_channels(buf: *mut u8, count: u32) -> u32 {
    let name = node_name();
    debug!("{{{}}}: wait_on_channels({:?}, {})", name, buf, count);
    if count == 0 {
        debug!("{{{}}}: wait_on_channels() -> ERR_INVALID_ARGS", name);
        return OakStatus::ERR_INVALID_ARGS.value() as u32;
    }

    // Accumulate the handles we're interested in.
    let size = oak_abi::SPACE_BYTES_PER_HANDLE * count as usize;
    let mut handle_data = Vec::<u8>::with_capacity(size);
    std::ptr::copy_nonoverlapping(buf, handle_data.as_mut_ptr(), size);
    handle_data.set_len(size);
    let mut handles = Vec::with_capacity(count as usize);
    let mut mem_reader = Cursor::new(handle_data);
    for _ in 0..count {
        let handle = mem_reader.read_u64::<byteorder::LittleEndian>().unwrap();
        let _b = mem_reader.read_u8().unwrap();
        handles.push(handle);
    }

    loop {
        // Check current handle status.
        let mut found_valid_handle = false;
        let mut found_ready_handle = false;
        for (i, handle) in handles.iter().enumerate() {
            let channel_status = RUNTIME
                .read()
                .expect(RUNTIME_MISSING)
                .node_channel_status(&name, *handle);
            if channel_status != oak::ChannelReadStatus::INVALID_CHANNEL {
                found_valid_handle = true;
            }
            if channel_status == oak::ChannelReadStatus::READ_READY {
                found_ready_handle = true;
            }

            // Write channel status back to the raw pointer.
            let p = buf
                .add(i * oak_abi::SPACE_BYTES_PER_HANDLE + (oak_abi::SPACE_BYTES_PER_HANDLE - 1));
            *p = channel_status
                .value()
                .try_into()
                .expect("failed to convert status to u8");
        }
        if RUNTIME.read().expect(RUNTIME_MISSING).termination_pending() {
            debug!("{{{}}}: wait_on_channels() -> ERR_TERMINATED", name);
            return OakStatus::ERR_TERMINATED.value() as u32;
        }
        if found_ready_handle {
            debug!("{{{}}}: wait_on_channels() -> OK", name);
            return OakStatus::OK.value() as u32;
        }
        if !found_valid_handle {
            debug!("{{{}}}: wait_on_channels() -> ERR_BAD_HANDLE", name);
            return OakStatus::ERR_BAD_HANDLE.value() as u32;
        }
        // We have at least one valid handle but no pending data, so wait and try again.
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
}

/// Test-only implementation of channel write functionality.
///
/// # Safety
///
/// The linear memory ranges [buf, buf+size) and [handle_buf, handle_buf+handle_count*8) must be
/// valid.
#[no_mangle]
pub unsafe extern "C" fn channel_write(
    handle: u64,
    buf: *const u8,
    size: usize,
    handle_buf: *const u8,
    handle_count: u32,
) -> u32 {
    let name = node_name();
    debug!(
        "{{{}}}: channel_write({}, {:?}, {}, {:?}, {})",
        name, handle, buf, size, handle_buf, handle_count
    );
    let mut msg = OakMessage {
        data: Vec::with_capacity(size),
        channels: Vec::with_capacity(handle_count as usize),
    };
    std::ptr::copy_nonoverlapping(buf, msg.data.as_mut_ptr(), size);
    msg.data.set_len(size);

    let handle_size = 8 * handle_count as usize;
    let mut handle_data = Vec::<u8>::with_capacity(handle_size);
    std::ptr::copy_nonoverlapping(handle_buf, handle_data.as_mut_ptr(), handle_size);
    handle_data.set_len(handle_size);

    let mut mem_reader = Cursor::new(handle_data);
    for _ in 0..handle_count as isize {
        let handle = mem_reader.read_u64::<byteorder::LittleEndian>().unwrap();
        let half = RUNTIME
            .read()
            .expect(RUNTIME_MISSING)
            .node_half_for_handle(&name, handle);
        match half {
            Some(half) => msg.channels.push(half),
            None => return OakStatus::ERR_BAD_HANDLE.value() as u32,
        }
    }

    let result = RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_channel_write(&name, handle, msg);
    debug!("{{{}}}: channel_write() -> {}", name, result);
    result
}

/// Test implementation of channel read functionality.
///
/// # Safety
///
/// The linear memory ranges [buf, buf+size) and [handle_buf, handle_buf+handle_count*8) must be
/// valid, as must the raw pointers actual_size and actual_handle_count.
#[no_mangle]
pub unsafe extern "C" fn channel_read(
    handle: u64,
    buf: *mut u8,
    size: usize,
    actual_size: *mut u32,
    handle_buf: *mut u8,
    handle_count: u32,
    actual_handle_count: *mut u32,
) -> u32 {
    let name = node_name();
    debug!(
        "{{{}}}: channel_read({}, {:?}, {}, {:?}, {:?}, {}, {:?})",
        name, handle, buf, size, actual_size, handle_buf, handle_count, actual_handle_count
    );
    let mut asize = 0u32;
    let mut acount = 0u32;
    let result = RUNTIME.write().expect(RUNTIME_MISSING).node_channel_read(
        &name,
        handle,
        size,
        &mut asize,
        handle_count,
        &mut acount,
    );
    *actual_size = asize;
    *actual_handle_count = acount;
    let msg = match result {
        Err(status) => {
            debug!("{{{}}}: channel_read() -> Err {}", name, status);
            return status;
        }
        Ok(msg) => msg,
    };
    std::ptr::copy_nonoverlapping(msg.data.as_ptr(), buf, asize as usize);
    let mut handle_data = Vec::with_capacity(8 * msg.channels.len());
    for half in msg.channels {
        let handle = RUNTIME
            .write()
            .expect(RUNTIME_MISSING)
            .node_add_half(&name, half);
        debug!("{{{}}}: channel_read() added handle {}", name, handle);
        handle_data
            .write_u64::<byteorder::LittleEndian>(handle)
            .unwrap();
    }
    std::ptr::copy_nonoverlapping(handle_data.as_ptr(), handle_buf, handle_data.len());

    debug!("{{{}}}: channel_read() -> OK", name);
    oak::OakStatus::OK as u32
}

/// Test version of channel creation.
///
/// # Safety
///
/// The raw pointers to linear memory must be valid.
#[no_mangle]
pub unsafe extern "C" fn channel_create(write: *mut u64, read: *mut u64) -> u32 {
    let name = node_name();
    debug!("{{{}}}: channel_create({:?}, {:?})", name, write, read);
    let (write_handle, read_handle) = RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_channel_create(&name);

    *write = write_handle;
    *read = read_handle;
    debug!(
        "{{{}}}: channel_create(*w={}, *r={}) -> OK",
        name, write_handle, read_handle
    );
    OakStatus::OK.value() as u32
}

/// Test version of channel closure.
#[no_mangle]
pub extern "C" fn channel_close(handle: u64) -> u32 {
    let name = node_name();
    debug!("{{{}}}: channel_close({})", name, handle);
    let result = RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_channel_close(&name, handle);
    debug!("{{{}}}: channel_close({}) -> {}", name, handle, result);
    result
}

/// Test implementation of dynamic Node creation.
///
/// # Safety
///
/// The linear memory ranges [config_buf, config_buf+config_len) and
/// [entrypoint_buf, entrypoint_buf+entrypoint_len) must be valid.
#[no_mangle]
pub unsafe fn node_create(
    config_buf: *const u8,
    config_len: usize,
    entrypoint_buf: *const u8,
    entrypoint_len: usize,

    handle: u64,
) -> u32 {
    let name = node_name();
    debug!(
        "{{{}}}: node_create({:?}, {}, {:?}, {}, {})",
        name, config_buf, config_len, entrypoint_buf, entrypoint_len, handle
    );

    let mut data = Vec::with_capacity(config_len as usize);
    std::ptr::copy_nonoverlapping(config_buf, data.as_mut_ptr(), config_len as usize);
    data.set_len(config_len as usize);
    let config = match String::from_utf8(data) {
        Err(_) => return OakStatus::ERR_INVALID_ARGS.value() as u32,
        Ok(s) => s,
    };

    let mut data = Vec::with_capacity(entrypoint_len as usize);
    std::ptr::copy_nonoverlapping(entrypoint_buf, data.as_mut_ptr(), entrypoint_len as usize);
    data.set_len(entrypoint_len as usize);
    let entrypoint = match String::from_utf8(data) {
        Err(_) => return OakStatus::ERR_INVALID_ARGS.value() as u32,
        Ok(s) => s,
    };
    debug!(
        "{{{}}}: node_create('{}', '{}', {})",
        name, config, entrypoint, handle
    );

    let start_info = match RUNTIME.write().expect(RUNTIME_MISSING).node_create(
        name,
        &config,
        &entrypoint,
        handle,
    ) {
        Err(status) => return status.value() as u32,
        Ok(result) => result,
    };

    debug!(
        "{{{}}}: start per-Node thread with handle {}",
        start_info.node_name, start_info.handle
    );
    let node_name_copy = start_info.node_name.to_string();
    let thread_handle = spawn(move || {
        set_node_name(start_info.node_name);
        (start_info.entrypoint)(start_info.handle)
    });
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_started(&node_name_copy, thread_handle);

    OakStatus::OK.value() as u32
}

/// Test version of random data generation.
///
/// # Safety
///
/// The linear memory range [buf, buf+size) must be valid.
#[no_mangle]
pub unsafe extern "C" fn random_get(buf: *mut u8, size: usize) -> u32 {
    let name = node_name();
    debug!("{{{}}}: random_get({:?}, {})", name, buf, size);
    let mut rng = rand::thread_rng();
    for i in 0..size as isize {
        *(buf.offset(i)) = rng.gen::<u8>();
    }
    debug!("{{{}}}: random_get() -> OK", name);
    OakStatus::OK.value() as u32
}

// Test helper functions that allow Node unit test code to manipulate
// the mock Oak environment.

/// Convenience test helper which returns the last message on a channel as a
/// string (without removing it from the channel), assuming that only a single
/// Node (with the default internal name) is present and under test.
pub fn last_message_as_string(handle: Handle) -> String {
    let result = match RUNTIME
        .read()
        .expect(RUNTIME_MISSING)
        .node_peek_message(DEFAULT_NODE_NAME, handle)
    {
        Some(data) => unsafe { std::str::from_utf8_unchecked(&data).to_string() },
        None => "".to_string(),
    };
    debug!("last message '{}'", result);
    result
}

/// Test helper that injects a failure for future channel read operations.
pub fn set_read_status(node_name: &str, handle: Handle, status: Option<u32>) {
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_set_read_status(node_name, handle, status);
}

/// Test helper that injects a failure for future channel write operations.
pub fn set_write_status(node_name: &str, handle: Handle, status: Option<u32>) {
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_set_write_status(node_name, handle, status);
}

/// Test helper that clears any handle to channel half mappings.
pub fn reset() {
    RUNTIME.write().expect(RUNTIME_MISSING).reset()
}

static LOG_INIT: Once = Once::new();

/// Test helper to initialize logging via simple_logger.
pub fn init_logging() {
    LOG_INIT.call_once(|| {
        simple_logger::init().unwrap();
        info!("Logging via simple_logger initialized");
    });
}

/// Start running the Application under test, with the given initial Node and
/// channel configuration.  Because multiple Nodes are linked into the same
/// test, the Nodes should be configured *not* to define the global extern "C"
/// oak_main(), as this would lead to duplicate symbols.  Instead, the
/// entrypoints map should provide a function pointer for each WasmConfiguration
/// entry in the configuration.
///
/// Also, Nodes under test should ensure that the oak_log crate does not end
/// being used for logging during tests, either by not calling oak_log::init()
/// at start-of-day (e.g. based on a build configuration), or by calling
/// oak_tests::init_logging() first, and ignoring the subsequent failure from
/// oak_log::init().
pub fn start(
    config: proto::manager::ApplicationConfiguration,
    entrypoints: HashMap<WasmEntrypointFullName, NodeMain, RandomState>,
) -> Option<()> {
    let (name, entrypoint, handle) = RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .configure(config, entrypoints)?;
    debug!("{{{}}}: start per-Node thread", name);
    let node_name = name.clone();
    let thread_handle = spawn(move || {
        set_node_name(node_name);
        entrypoint(handle)
    });
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_started(&name, thread_handle);
    Some(())
}

/// Start running a test of a single-Node Application.
pub fn start_node(handle: Handle, entrypoint: NodeMain) {
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .set_termination_pending(false);
    debug!("start per-Node thread with handle {}", handle);
    let node_name = DEFAULT_NODE_NAME.to_string();
    let main_handle = spawn(move || {
        set_node_name(node_name);
        entrypoint(handle)
    });
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .node_started(DEFAULT_NODE_NAME, main_handle)
}

/// Stop the running Application under test.
pub fn stop() {
    info!("stop all running Node threads");
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .set_termination_pending(true);

    loop {
        let (name, thread_handle) = match RUNTIME.write().expect(RUNTIME_MISSING).stop_next() {
            None => break,
            Some(x) => x,
        };
        debug!("{{{}}}: await thread join", name);
        thread_handle.join().expect("could not join thread");
        debug!("{{{}}}: thread completed", name);
    }
    reset();
}

/// Test helper to set up a channel into the (single) Node under test for
/// injected gRPC requests.
pub fn grpc_channel_setup_default() -> Handle {
    RUNTIME
        .write()
        .expect(RUNTIME_MISSING)
        .grpc_channel_setup(DEFAULT_NODE_NAME)
}

/// Test helper to inject a (single) gRPC request message to the Node
/// under test, and collect a (single) response.
pub fn inject_grpc_request<R, Q>(method_name: &str, req: R) -> oak::grpc::Result<Q>
where
    R: protobuf::Message,
    Q: protobuf::Message,
{
    // Put the request in a GrpcRequest wrapper and serialize into a message.
    let mut grpc_req = oak::proto::grpc_encap::GrpcRequest::new();
    grpc_req.set_method_name(method_name.to_string());
    let mut any = protobuf::well_known_types::Any::new();
    if let Err(e) = req.write_to_writer(&mut any.value) {
        warn!("failed to serialize gRPC request: {}", e);
        return Err(oak::grpc::build_status(
            oak::grpc::Code::INTERNAL,
            "failed to serialize gRPC request",
        ));
    }
    grpc_req.set_req_msg(any);
    grpc_req.set_last(true);
    let mut req_msg = OakMessage {
        data: Vec::new(),
        channels: Vec::new(),
    };
    grpc_req
        .write_to_writer(&mut req_msg.data)
        .expect("failed to serialize GrpcRequest message");

    // Create a new channel to hold the request message.
    let (mut req_write_half, req_read_half) = RUNTIME.write().expect(RUNTIME_MISSING).new_channel();
    let status = req_write_half.write_message(req_msg);
    if status != oak::OakStatus::OK.value() as u32 {
        panic!("could not write message (status: {})", status);
    }

    // Create a new channel for responses to arrive on and also attach that to the message.
    let (rsp_write_half, mut rsp_read_half) = RUNTIME.write().expect(RUNTIME_MISSING).new_channel();

    // Create a notification message and attach the method-invocation specific channels to it.
    let notify_msg = OakMessage {
        data: Vec::new(),
        channels: vec![req_read_half, rsp_write_half],
    };

    // Send the notification message (with attached handles) into the Node under test.
    let grpc_channel = RUNTIME
        .read()
        .expect(RUNTIME_MISSING)
        .grpc_channel()
        .expect("no gRPC notification channel setup");
    let status = grpc_channel
        .write()
        .expect("corrupt gRPC channel ref")
        .write_message(notify_msg);
    if status != oak::OakStatus::OK.value() as u32 {
        panic!("could not write message (status: {})", status);
    }

    // Read the serialized, encapsulated response.
    loop {
        let mut size = 0u32;
        let mut count = 0u32;
        let result =
            rsp_read_half.read_message(std::usize::MAX, &mut size, std::u32::MAX, &mut count);
        let rsp = match result {
            Err(e) => {
                if e == OakStatus::ERR_CHANNEL_EMPTY.value() as u32 {
                    info!("no pending gRPC response message; poll again soon");
                    std::thread::sleep(std::time::Duration::from_millis(100));
                    continue;
                } else {
                    panic!("failed to read from response channel: {}", e);
                }
            }
            Ok(r) => r,
        };
        if rsp.data.is_empty() {
            info!("no pending message; poll again soon");
            std::thread::sleep(std::time::Duration::from_millis(100));
            continue;
        }
        let mut rsp: oak::proto::grpc_encap::GrpcResponse =
            protobuf::parse_from_bytes(&rsp.data).expect("failed to parse GrpcResponse message");
        if !rsp.last {
            panic!("Expected single final response");
        }

        if rsp.get_status().code != oak::grpc::Code::OK.value() {
            return Err(rsp.take_status());
        }
        let rsp: Q = protobuf::parse_from_bytes(&rsp.get_rsp_msg().value)
            .expect("Failed to parse response protobuf message");
        return Ok(rsp);
    }
}
