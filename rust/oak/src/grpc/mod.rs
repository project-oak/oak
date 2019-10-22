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

//! Functionality to help Oak Nodes interact with gRPC.

use crate::{proto, wasm, Handle, OakStatus, ReadHandle, WriteHandle};
use protobuf::{Message, ProtobufEnum};

/// Result type that uses a [`proto::status::Status`] type for error values.
pub type Result<T> = std::result::Result<T, proto::status::Status>;

/// Trait to allow repeated writing of responses for server-streaming gRPC methods.
pub trait ResponseWriter<T: protobuf::Message> {
    fn write(&mut self, rsp: T);
}

/// Implementation of [`ResponseWriter`] that encapsulates response messages
/// into `GrpcResponse` wrapper messages and writes serialized versions to a
/// (mutably borrowed) send channel.
pub struct ChannelResponseWriter<'a> {
    pub channel: &'a mut crate::io::Channel,
}

impl<'a, T> ResponseWriter<T> for ChannelResponseWriter<'a>
where
    T: protobuf::Message,
{
    fn write(&mut self, rsp: T) {
        // Put the serialized response into a GrpcResponse message wrapper.
        let mut grpc_rsp = proto::grpc_encap::GrpcResponse::new();
        let mut any = protobuf::well_known_types::Any::new();
        rsp.write_to_writer(&mut any.value).unwrap();
        grpc_rsp.set_rsp_msg(any);
        // Serialize the GrpcResponse into the send channel.
        grpc_rsp.write_to_writer(&mut self.channel).unwrap();
    }
}

/// Trait for Oak Nodes that act as a gRPC services.
///
/// An `OakNode` instance is normally passed to [`event_loop`], to allow
/// repeated invocation of its `invoke()` method.
pub trait OakNode {
    /// Construct the (single) instance of the node.
    ///
    /// This method may choose to initialize logging by invoking
    /// [`oak_log::init()`].
    ///
    /// [`oak_log::init()`]: ../../oak_log/fn.init.html
    fn new() -> Self
    where
        Self: Sized;

    /// Process a single gRPC method invocation.
    ///
    /// The method name is provided by `method` and the incoming serialized gRPC
    /// request is held in `req`.  Response messages should be written to `out`,
    /// as serialized [`GrpcResponse`] messages encapsulating the service
    /// response.
    ///
    /// [`GrpcResponse`]: crate::proto::grpc_encap::GrpcResponse
    fn invoke(&mut self, method: &str, req: &[u8], out: WriteHandle);
}

/// Perform a gRPC event loop for a Node.
///
/// Invoking the given `node`'s [`invoke`] method for each incoming request that
/// arrives on the inbound channel as a serialized [`GrpcRequest`] message,
/// giving the [`invoke`] method the outbound channel for encapsulated responses
/// to be written to.
///
/// [`invoke`]: OakNode::invoke
/// [`GrpcRequest`]: crate::proto::grpc_encap::GrpcRequest
pub fn event_loop<T: OakNode>(
    mut node: T,
    grpc_in_handle: ReadHandle,
    grpc_out_handle: WriteHandle,
) -> i32 {
    info!(
        "start event loop for node with handles in:{:?} out:{:?}",
        grpc_in_handle, grpc_out_handle
    );
    if grpc_in_handle.handle == 0 || grpc_out_handle.handle == 0 {
        return OakStatus::ERR_CHANNEL_CLOSED.value();
    }
    crate::set_panic_hook();

    let read_handles = vec![grpc_in_handle];
    let mut space = crate::new_handle_space(&read_handles);

    loop {
        // Block until there is a message to read on an input channel.
        crate::prep_handle_space(&mut space);
        unsafe {
            let status = wasm::wait_on_channels(space.as_mut_ptr(), read_handles.len() as u32);
            match OakStatus::from_i32(status as i32) {
                Some(OakStatus::OK) => (),
                Some(err) => return err as i32,
                None => return OakStatus::OAK_STATUS_UNSPECIFIED.value(),
            }
        }

        let mut buf = Vec::<u8>::with_capacity(1024);
        let mut handles = Vec::<Handle>::with_capacity(1);
        crate::channel_read(grpc_in_handle, &mut buf, &mut handles);
        if buf.is_empty() {
            info!("no pending message; poll again");
            continue;
        }
        if !handles.is_empty() {
            panic!("unexpected handles received alongside gRPC response")
        }
        let req: proto::grpc_encap::GrpcRequest = protobuf::parse_from_bytes(&buf).unwrap();
        if !req.last {
            panic!("Support for streaming requests not yet implemented");
        }
        node.invoke(
            &req.method_name,
            req.get_req_msg().value.as_slice(),
            grpc_out_handle,
        );
    }
}
