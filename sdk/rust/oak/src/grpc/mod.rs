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

pub use crate::proto::code::Code;
use crate::{proto, Handle, OakError, OakStatus, ReadHandle, WriteHandle};
use log::info;
use protobuf::{Message, ProtobufEnum};

/// Result type that uses a [`proto::status::Status`] type for error values.
pub type Result<T> = std::result::Result<T, proto::status::Status>;

/// Helper to create a gRPC status object.
pub fn build_status(code: Code, msg: &str) -> proto::status::Status {
    let mut status = proto::status::Status::new();
    status.set_code(code.value());
    status.set_message(msg.to_string());
    status
}

/// Channel-holding object that encapsulates response messages into
/// `GrpcResponse` wrapper messages and writes serialized versions to a send
///  channel.
pub struct ChannelResponseWriter {
    channel: crate::io::Sender<proto::grpc_encap::GrpcResponse>,
}

impl crate::io::Encodable for proto::grpc_encap::GrpcResponse {
    fn encode(&self) -> std::result::Result<crate::io::Message, crate::OakError> {
        let bytes = self.write_to_bytes()?;
        let handles = Vec::new();
        Ok(crate::io::Message { bytes, handles })
    }
}

/// Indicate whether a write method should leave the current gRPC method
/// invocation open or close it.
#[derive(PartialEq, Clone, Debug)]
pub enum WriteMode {
    KeepOpen,
    Close,
}

impl ChannelResponseWriter {
    pub fn new(out_handle: crate::WriteHandle) -> Self {
        ChannelResponseWriter {
            channel: crate::io::Sender::new(out_handle),
        }
    }

    /// Retrieve the Oak handle underlying the writer object.
    pub fn handle(self) -> crate::WriteHandle {
        self.channel.handle
    }

    /// Write out a gRPC response and optionally close out the method
    /// invocation.  Any errors from the channel are silently dropped.
    pub fn write<T: protobuf::Message>(
        &mut self,
        rsp: &T,
        mode: WriteMode,
    ) -> std::result::Result<(), OakError> {
        // Put the serialized response into a GrpcResponse message wrapper and
        // serialize it into the channel.
        let mut grpc_rsp = proto::grpc_encap::GrpcResponse::new();
        let mut any = protobuf::well_known_types::Any::new();
        rsp.write_to_writer(&mut any.value)?;
        grpc_rsp.set_rsp_msg(any);
        grpc_rsp.set_last(match mode {
            WriteMode::KeepOpen => false,
            WriteMode::Close => true,
        });
        self.channel.send(&grpc_rsp)?;
        if mode == WriteMode::Close {
            self.channel.close()?;
        }
        Ok(())
    }

    /// Write an empty gRPC response and optionally close out the method
    /// invocation. Any errors from the channel are silently dropped.
    pub fn write_empty(&mut self, mode: WriteMode) -> std::result::Result<(), OakError> {
        let mut grpc_rsp = proto::grpc_encap::GrpcResponse::new();
        grpc_rsp.set_rsp_msg(protobuf::well_known_types::Any::new());
        grpc_rsp.set_last(match mode {
            WriteMode::KeepOpen => false,
            WriteMode::Close => true,
        });
        self.channel.send(&grpc_rsp)?;
        if mode == WriteMode::Close {
            self.channel.close()?;
        }
        Ok(())
    }

    /// Close out the gRPC method invocation with the given final result.
    pub fn close(&mut self, result: Result<()>) -> std::result::Result<(), OakError> {
        // Build a final GrpcResponse message wrapper and serialize it into the
        // channel.
        let mut grpc_rsp = proto::grpc_encap::GrpcResponse::new();
        grpc_rsp.set_last(true);
        if let Err(status) = result {
            grpc_rsp.set_status(status);
        }
        self.channel.send(&grpc_rsp)?;
        self.channel.close()?;
        Ok(())
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
    /// request is held in `req`.  Response messages should be written using
    /// `writer.write`, followed by `writer.close`.
    fn invoke(&mut self, method: &str, req: &[u8], writer: ChannelResponseWriter);
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
) -> std::result::Result<(), crate::OakStatus> {
    info!("start event loop for node with handle {:?}", grpc_in_handle);
    if !grpc_in_handle.handle.is_valid() {
        return Err(OakStatus::ERR_CHANNEL_CLOSED);
    }
    let read_handles = vec![grpc_in_handle];
    let mut space = crate::new_handle_space(&read_handles);

    loop {
        // Block until there is a message to read on an input channel.
        crate::prep_handle_space(&mut space);
        // TODO: Use higher-level wait function from SDK instead of the ABI one.
        let status =
            unsafe { oak_abi::wait_on_channels(space.as_mut_ptr(), read_handles.len() as u32) };
        crate::result_from_status(status as i32, ())?;

        let mut buf = Vec::<u8>::with_capacity(1024);
        let mut handles = Vec::<Handle>::with_capacity(1);
        crate::channel_read(grpc_in_handle, &mut buf, &mut handles)?;
        if buf.is_empty() {
            panic!("no bytes received")
        }
        if handles.is_empty() {
            panic!("no response handle received alongside gRPC request")
        }
        let req: proto::grpc_encap::GrpcRequest =
            protobuf::parse_from_bytes(&buf).expect("failed to parse GrpcRequest message");
        if !req.last {
            panic!("Support for streaming requests not yet implemented");
        }
        node.invoke(
            &req.method_name,
            req.get_req_msg().value.as_slice(),
            ChannelResponseWriter::new(WriteHandle { handle: handles[0] }),
        );
    }
}

/// Generic function that handles request deserialization and response
/// serialization (and sending down a channel) for a function that handles a
/// request/response pair.
///
/// Panics if [de-]serialization or channel operations fail.
pub fn handle_req_rsp<C, R, Q>(mut node_fn: C, req: &[u8], mut writer: ChannelResponseWriter)
where
    C: FnMut(R) -> Result<Q>,
    R: protobuf::Message,
    Q: protobuf::Message,
{
    let r: R = protobuf::parse_from_bytes(&req).expect("Failed to parse request protobuf message");
    let result = match node_fn(r) {
        Ok(rsp) => writer.write(&rsp, WriteMode::Close),
        Err(status) => writer.close(Err(status)),
    };
    if let Err(e) = result {
        panic!("Failed to process response: {:?}", e)
    }
}

/// Generic function that handles request deserialization and response
/// serialization (and sending down a channel) for a function that handles a
/// request and streams responses.
///
/// Panics if [de-]serialization or channel operations fail.
pub fn handle_req_stream<C, R>(mut node_fn: C, req: &[u8], writer: ChannelResponseWriter)
where
    C: FnMut(R, ChannelResponseWriter),
    R: protobuf::Message,
{
    let r: R = protobuf::parse_from_bytes(&req).expect("Failed to parse request protobuf message");
    node_fn(r, writer)
}

/// Generic function that handles request deserialization and response
/// serialization (and sending down a channel) for a function that handles a
/// stream of requests to produce a response.
///
/// Panics if [de-]serialization or channel operations fail.
pub fn handle_stream_rsp<C, R, Q>(mut node_fn: C, req: &[u8], mut writer: ChannelResponseWriter)
where
    C: FnMut(Vec<R>) -> Result<Q>,
    R: protobuf::Message,
    Q: protobuf::Message,
{
    // TODO(#97): better client-side streaming
    let rr: Vec<R> =
        vec![protobuf::parse_from_bytes(&req).expect("Failed to parse request protobuf message")];
    let result = match node_fn(rr) {
        Ok(rsp) => writer.write(&rsp, WriteMode::Close),
        Err(status) => writer.close(Err(status)),
    };
    if let Err(e) = result {
        panic!("Failed to process response: {:?}", e)
    }
}

/// Generic function that handles request deserialization and response
/// serialization (and sending down a channel) for a function that handles a
/// stream of requests to produce a stream of responses.
///
/// Panics if [de-]serialization or channel operations fail.
pub fn handle_stream_stream<C, R>(mut node_fn: C, req: &[u8], writer: ChannelResponseWriter)
where
    C: FnMut(Vec<R>, ChannelResponseWriter),
    R: protobuf::Message,
{
    // TODO(#97): better client-side streaming
    let rr: Vec<R> =
        vec![protobuf::parse_from_bytes(&req).expect("Failed to parse request protobuf message")];
    node_fn(rr, writer)
}
