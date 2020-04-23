//
// Copyright 2020 The Project Oak Authors
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

use byteorder::{ReadBytesExt, WriteBytesExt};
use lazy_static::lazy_static;
use log::{debug, error, info, warn};
use oak_abi::OakStatus;
use oak_runtime::{
    proto::oak::application::ApplicationConfiguration, runtime::RuntimeProxy, NodeId,
};
use prost::Message;
use std::{convert::TryInto, io::Cursor, sync::RwLock};

#[no_mangle]
pub extern "C" fn glue_init(debug: u32) {
    let _ = ::std::panic::catch_unwind(|| {
        if debug != 0 {
            simple_logger::init_with_level(log::Level::Debug).expect("failed to initialize logger");
        }
        info!("Rust FFI glue initialized");
    });
}

type NodeFactory =
    extern "C" fn(data: usize, name: *const u8, name_len: u32, node_id: u64, handle: u64) -> ();

struct Glue {
    runtime: oak_runtime::RuntimeProxy,
    factory: Option<NodeFactory>,
    factory_data: usize,
}

impl Glue {
    fn new(
        runtime: oak_runtime::RuntimeProxy,
        factory: Option<NodeFactory>,
        factory_data: usize,
    ) -> Self {
        Glue {
            runtime,
            factory,
            factory_data,
        }
    }
}

lazy_static! {
    static ref GLUE: RwLock<Option<Glue>> = RwLock::new(None);
}

const R1: &str = "global glue lock poisoned";
const R2: &str = "global glue object missing";

/// Recreate a RuntimeProxy instance that corresponds to the given node ID
/// value.
fn proxy_for_node(node_id: u64) -> RuntimeProxy {
    GLUE.read()
        .expect(R1)
        .as_ref()
        .expect(R2)
        .runtime
        .new_for_node(NodeId(node_id))
}

/// Start the Rust runtime, with the ApplicationConfiguration provided in
/// serialized form.
///
/// # Safety
///
/// Caller must ensure that the memory range [config_buf, config_buf+config_len) is
/// accessible and holds a protobuf-serialized ApplicationConfiguration message.
#[no_mangle]
pub unsafe extern "C" fn glue_start(
    config_buf: *const u8,
    config_len: u32,
    factory: Option<NodeFactory>,
    factory_data: usize,
    node_id: *mut u64,
) -> u64 {
    std::panic::catch_unwind(|| {
        let config_data = std::slice::from_raw_parts(config_buf, config_len as usize);

        let app_config = match ApplicationConfiguration::decode(config_data) {
            Ok(c) => c,
            Err(e) => {
                error!("Failed to decode ApplicationConfiguration: {}", e);
                return oak_abi::INVALID_HANDLE;
            }
        };
        let runtime_config = oak_runtime::RuntimeConfiguration {
            metrics_port: Some(3030),
            introspect_port: Some(1909),
        };
        info!(
            "start runtime with initial config {}.{} {:?}",
            app_config.initial_node_config_name, app_config.initial_entrypoint_name, runtime_config
        );

        // Register callback for creating C++ pseudo-Nodes.
        oak_runtime::node::external::register_factory(create_and_run_node);
        info!("register oak_glue::create_and_run_node() as node factory");

        // Configure the Rust Runtime, and run the gRPC server pseudo-Node as the implicit
        // initial Node.
        let (grpc_proxy, grpc_handle) =
            match oak_runtime::configure_and_run(app_config, runtime_config) {
                Ok(p) => p,
                Err(status) => {
                    error!("Failed to start runtime: {:?}", status);
                    return oak_abi::INVALID_HANDLE;
                }
            };
        *node_id = grpc_proxy.node_id.0;
        info!(
            "runtime started, grpc_node_id={}, grpc_handle={}",
            *node_id, grpc_handle
        );

        let glue = Glue::new(grpc_proxy, factory, factory_data);
        *GLUE.write().expect(R1) = Some(glue);
        grpc_handle
    })
    .unwrap_or(oak_abi::INVALID_HANDLE)
}

/// Stop the Rust runtime.
#[no_mangle]
pub extern "C" fn glue_stop() {
    let mut glue = GLUE.write().expect(R1);
    info!(
        "runtime graph at exit:\n\n{}",
        glue.as_ref().expect(R2).runtime.graph_runtime()
    );
    warn!("stopping Rust runtime");
    glue.as_ref().expect(R2).runtime.stop_runtime();
    *glue = None;
}

/// See [`oak_abi::wait_on_channels`].
///
/// # Safety
///
/// The memory range [buf, buf+count*SPACE_BYTES_PER_HANDLE) must be
/// valid.
#[no_mangle]
pub unsafe extern "C" fn glue_wait_on_channels(node_id: u64, buf: *mut u8, count: u32) -> u32 {
    std::panic::catch_unwind(|| {
        debug!(
            "{{{}}}: wait_on_channels(buf={:?}, count={})",
            node_id, buf, count
        );

        // Accumulate the handles we're interested in.
        let size = oak_abi::SPACE_BYTES_PER_HANDLE * count as usize;
        let mut handle_data = Vec::<u8>::with_capacity(size);
        std::ptr::copy_nonoverlapping(buf, handle_data.as_mut_ptr(), size);
        handle_data.set_len(size);
        let mut handles = Vec::with_capacity(count as usize);
        let mut mem_reader = Cursor::new(handle_data);
        for _ in 0..count {
            // Retrieve the 8-byte handle value and skip over the 1 byte status
            // value.
            let handle = mem_reader.read_u64::<byteorder::LittleEndian>().unwrap();
            let _b = mem_reader.read_u8().unwrap();
            debug!("{{{}}}: wait_on_channels   handle {:?}", node_id, handle);
            handles.push(handle);
        }

        let proxy = proxy_for_node(node_id);
        let channel_statuses = match proxy.wait_on_channels(&handles) {
            Ok(r) => r,
            Err(s) => return s as u32,
        };

        if channel_statuses.len() != handles.len() {
            error!(
                "length mismatch: submitted {} handles, got {} results",
                handles.len(),
                channel_statuses.len()
            );
            return OakStatus::ErrInternal as u32;
        }
        for (i, channel_status) in channel_statuses.iter().enumerate() {
            // Write channel status back to the raw pointer.
            let p = buf
                .add(i * oak_abi::SPACE_BYTES_PER_HANDLE + (oak_abi::SPACE_BYTES_PER_HANDLE - 1));

            *p = *channel_status as u8;
        }
        OakStatus::Ok as u32
    })
    .unwrap_or(OakStatus::ErrInternal as u32)
}

/// See [`oak_abi::channel_read`].
///
/// # Safety
///
/// The memory ranges [buf, buf+size) and [handle_buf, handle_buf+handle_count*8) must be
/// valid, as must the raw pointers actual_size and actual_handle_count.
#[no_mangle]
pub unsafe extern "C" fn glue_channel_read(
    node_id: u64,
    handle: u64,
    buf: *mut u8,
    size: usize,
    actual_size: *mut u32,
    handle_buf: *mut u8,
    handle_count: u32,
    actual_handle_count: *mut u32,
) -> u32 {
    debug!(
        "{{{}}}: channel_read(h={}, buf={:?}, size={}, &actual_size={:?}, handle_buf={:?}, count={}, &actual_count={:?})",
        node_id, handle, buf, size, actual_size, handle_buf, handle_count, actual_handle_count
    );

    let proxy = proxy_for_node(node_id);
    let msg = match proxy.channel_try_read_message(handle, size, handle_count as usize) {
        Ok(msg) => msg,
        Err(status) => return status as u32,
    };

    let result = match msg {
        None => {
            *actual_size = 0;
            *actual_handle_count = 0;
            OakStatus::ErrChannelEmpty
        }
        Some(oak_runtime::runtime::NodeReadStatus::Success(msg)) => {
            *actual_size = msg.data.len().try_into().unwrap();
            *actual_handle_count = msg.handles.len().try_into().unwrap();
            std::ptr::copy_nonoverlapping(msg.data.as_ptr(), buf, msg.data.len());
            let mut handle_data = Vec::with_capacity(8 * msg.handles.len());
            for handle in msg.handles {
                debug!("{{{}}}: channel_read() added handle {}", node_id, handle);
                handle_data
                    .write_u64::<byteorder::LittleEndian>(handle)
                    .unwrap();
            }
            std::ptr::copy_nonoverlapping(handle_data.as_ptr(), handle_buf, handle_data.len());
            OakStatus::Ok
        }
        Some(oak_runtime::runtime::NodeReadStatus::NeedsCapacity(a, b)) => {
            *actual_size = a.try_into().unwrap();
            *actual_handle_count = b.try_into().unwrap();
            if a > size as usize {
                OakStatus::ErrBufferTooSmall
            } else {
                OakStatus::ErrHandleSpaceTooSmall
            }
        }
    };

    debug!("{{{}}}: channel_read() -> {:?}", node_id, result);
    result as u32
}

/// See [`oak_abi::channel_write`].
///
/// # Safety
///
/// The memory ranges [buf, buf+size) and [handle_buf, handle_buf+handle_count*8) must be
/// valid.
#[no_mangle]
pub unsafe extern "C" fn glue_channel_write(
    node_id: u64,
    handle: u64,
    buf: *const u8,
    size: usize,
    handle_buf: *const u8,
    handle_count: u32,
) -> u32 {
    debug!(
        "{{{}}}: channel_write(h={}, buf={:?}, size={}, handle_buf={:?}, count={})",
        node_id, handle, buf, size, handle_buf, handle_count
    );
    let mut msg = oak_runtime::NodeMessage {
        data: Vec::with_capacity(size),
        handles: Vec::with_capacity(handle_count as usize),
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
        debug!("{{{}}}: channel_write   include handle {}", node_id, handle);
        msg.handles.push(handle);
    }

    let proxy = proxy_for_node(node_id);
    let result = proxy.channel_write(handle, msg);
    debug!("{{{}}}: channel_write() -> {:?}", node_id, result);
    match result {
        Ok(_) => OakStatus::Ok as u32,
        Err(status) => status as u32,
    }
}

/// See [`oak_abi::channel_create`].
///
/// # Safety
///
/// The raw pointers to memory must be valid.
#[no_mangle]
pub unsafe extern "C" fn glue_channel_create(node_id: u64, write: *mut u64, read: *mut u64) -> u32 {
    debug!("{{{}}}: channel_create({:?}, {:?})", node_id, write, read);
    let proxy = proxy_for_node(node_id);
    let (write_handle, read_handle) =
        proxy.channel_create(&oak_abi::label::Label::public_trusted());
    *write = write_handle;
    *read = read_handle;
    debug!(
        "{{{}}}: channel_create(*w={:?}, *r={:?}) -> OK",
        node_id, write_handle, read_handle
    );
    OakStatus::Ok as u32
}

/// See [`oak_abi::channel_close`].
#[no_mangle]
pub extern "C" fn glue_channel_close(node_id: u64, handle: u64) -> u32 {
    debug!("{{{}}}: channel_close({})", node_id, handle);
    let proxy = proxy_for_node(node_id);
    let result = proxy.channel_close(handle);
    debug!("{{{}}}: channel_close({}) -> {:?}", node_id, handle, result);
    match result {
        Ok(_) => OakStatus::Ok as u32,
        Err(status) => status as u32,
    }
}

fn create_and_run_node(config_name: &str, node_id: NodeId, handle: oak_abi::Handle) {
    info!(
        "invoke registered factory with '{}', node_id={:?}, handle={}",
        config_name, node_id, handle
    );
    let factory = GLUE.read().expect(R1).as_ref().expect(R2).factory;
    let factory_data = GLUE.read().expect(R1).as_ref().expect(R2).factory_data;
    factory.expect("no factory registered!")(
        factory_data,
        config_name.as_ptr(),
        config_name.len() as u32,
        node_id.0,
        handle,
    );
}
