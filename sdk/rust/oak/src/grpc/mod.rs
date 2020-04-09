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

use crate::{OakError, OakStatus};
use log::error;
use oak_abi::proto::google::rpc;
pub use oak_abi::proto::google::rpc::*;
pub use oak_abi::proto::oak::encap::{GrpcRequest, GrpcResponse};

pub mod client;
mod invocation;
pub use invocation::Invocation;

/// Result type that uses a [`proto::status::Status`] type for error values.
pub type Result<T> = std::result::Result<T, rpc::Status>;

/// Helper to create a gRPC status object.
pub fn build_status(code: rpc::Code, msg: &str) -> rpc::Status {
    rpc::Status {
        code: code as i32,
        message: msg.to_owned(),
        details: vec![],
    }
}

/// Channel-holding object that encapsulates response messages into
/// `GrpcResponse` wrapper messages and writes serialized versions to a send
/// channel.
pub struct ChannelResponseWriter {
    sender: crate::io::Sender<GrpcResponse>,
}

/// Indicate whether a write method should leave the current gRPC method
/// invocation open or close it.
#[derive(PartialEq, Clone, Debug)]
pub enum WriteMode {
    KeepOpen,
    Close,
}

impl ChannelResponseWriter {
    pub fn new(sender: crate::io::Sender<GrpcResponse>) -> Self {
        ChannelResponseWriter { sender }
    }

    /// Retrieve the Oak handle underlying the writer object.
    pub fn handle(self) -> crate::WriteHandle {
        self.sender.handle
    }

    /// Write out a gRPC response and optionally close out the method
    /// invocation.  Any errors from the channel are silently dropped.
    pub fn write<T: prost::Message>(
        &mut self,
        rsp: &T,
        mode: WriteMode,
    ) -> std::result::Result<(), OakError> {
        // Put the serialized response into a GrpcResponse message wrapper and
        // serialize it into the channel.
        let mut grpc_rsp = GrpcResponse::default();
        let mut any = prost_types::Any::default();
        rsp.encode(&mut any.value)?;
        grpc_rsp.rsp_msg = Some(any);
        grpc_rsp.last = match mode {
            WriteMode::KeepOpen => false,
            WriteMode::Close => true,
        };
        self.sender.send(&grpc_rsp)?;
        if mode == WriteMode::Close {
            self.sender.close()?;
        }
        Ok(())
    }

    /// Write an empty gRPC response and optionally close out the method
    /// invocation. Any errors from the channel are silently dropped.
    pub fn write_empty(&mut self, mode: WriteMode) -> std::result::Result<(), OakError> {
        let mut grpc_rsp = GrpcResponse::default();
        grpc_rsp.rsp_msg = Some(prost_types::Any::default());
        grpc_rsp.last = match mode {
            WriteMode::KeepOpen => false,
            WriteMode::Close => true,
        };
        self.sender.send(&grpc_rsp)?;
        if mode == WriteMode::Close {
            self.sender.close()?;
        }
        Ok(())
    }

    /// Close out the gRPC method invocation with the given final result.
    pub fn close(&mut self, result: Result<()>) -> std::result::Result<(), OakError> {
        // Build a final GrpcResponse message wrapper and serialize it into the
        // channel.
        let mut grpc_rsp = GrpcResponse::default();
        grpc_rsp.last = true;
        if let Err(status) = result {
            grpc_rsp.status = Some(status);
        }
        self.sender.send(&grpc_rsp)?;
        self.sender.close()?;
        Ok(())
    }
}

/// Trait for Oak Nodes that act as a gRPC services.
///
/// A `ServerNode` instance is normally passed to [`oak::run_event_loop`], to
/// allow repeated invocation of its `invoke()` method.
///
/// You can choose to implement this trait yourself, or use the convenient
/// `Dispatcher` created by the gRPC code generator.
///
/// [`oak::run_event_loop`]: ../../oak/fn.run_event_loop.html
pub trait ServerNode {
    /// Process a single gRPC method invocation.
    ///
    /// The method name is provided by `method` and the incoming serialized gRPC
    /// request is held in `req`.  Response messages should be written using
    /// `writer.write`, followed by `writer.close`.
    fn invoke(&mut self, method: &str, req: &[u8], writer: ChannelResponseWriter);
}

impl<T: ServerNode> crate::Node<Invocation> for T {
    /// Handle incoming gRPC events for an [`ServerNode`].
    ///
    /// Invoking the given `node`'s [`invoke`] method for each incoming request that
    /// arrives on the inbound channel as a serialized [`Invocation`] object,
    /// giving the [`invoke`] method the outbound channel for encapsulated responses
    /// to be written to.
    ///
    /// [`invoke`]: ServerNode::invoke
    fn handle_command(
        &mut self,
        invocation: Invocation,
    ) -> std::result::Result<(), crate::OakError> {
        // Read a single encapsulated request message from the read half.
        let req: GrpcRequest = invocation.request_receiver.receive()?;
        // Since we are expecting a single message, close the channel immediately.
        // This will change when we implement client streaming (#97).
        invocation.request_receiver.close()?;
        if !req.last {
            // TODO(#97): Implement client streaming.
            panic!("Support for streaming requests not yet implemented");
        }
        self.invoke(
            &req.method_name,
            req.req_msg
                .map(|any| any.value)
                .unwrap_or_default()
                .as_slice(),
            ChannelResponseWriter::new(invocation.response_sender),
        );
        Ok(())
    }
}

/// Extract a protocol buffer message from a GrpcResponse wrapper.
/// Returns the message together with an indicator of whether this is the last
/// response.
pub fn decap_response<T: prost::Message + Default>(grpc_rsp: GrpcResponse) -> Result<(T, bool)> {
    let status = grpc_rsp.status.unwrap_or_default();
    if status.code != rpc::Code::Ok as i32 {
        return Err(status);
    }
    let bytes = grpc_rsp.rsp_msg.unwrap_or_default().value;
    let rsp = T::decode(bytes.as_slice()).map_err(|proto_err| {
        build_status(
            rpc::Code::InvalidArgument,
            &format!("message parsing failed: {}", proto_err),
        )
    })?;
    Ok((rsp, grpc_rsp.last))
}

/// Helper to inject a (single) gRPC request message via a notification channel,
/// in the same manner as the gRPC pseudo-Node does, and return a channel for
/// reading responses from.
pub fn invoke_grpc_method_stream<R>(
    method_name: &str,
    req: &R,
    req_type_url: Option<&str>,
    invocation_channel: &crate::io::Sender<Invocation>,
) -> Result<crate::io::Receiver<GrpcResponse>>
where
    R: prost::Message,
{
    // Create a new channel for request message delivery.
    let (req_sender, req_receiver) =
        crate::io::channel_create::<GrpcRequest>().expect("failed to create channel");

    // Put the request in a GrpcRequest wrapper and send it into the request
    // message channel.
    let req = oak_abi::grpc::encap_request(req, req_type_url, method_name)
        .expect("failed to serialize GrpcRequest");
    req_sender.send(&req).expect("failed to write to channel");
    req_sender.close().expect("failed to close channel");

    // Create a new channel for responses to arrive on.
    let (rsp_sender, rsp_receiver) =
        crate::io::channel_create::<GrpcResponse>().expect("failed to create channel");

    // Build an Invocation holding the two channels and send it down the
    // specified channel.
    let invocation = Invocation {
        request_receiver: req_receiver.clone(),
        response_sender: rsp_sender.clone(),
    };
    invocation_channel
        .send(&invocation)
        .expect("failed to write invocation to channel");
    req_receiver.close().expect("failed to close channel");
    rsp_sender.close().expect("failed to close channel");

    Ok(rsp_receiver)
}

/// Helper to inject a (single) gRPC request message via a notification channel,
/// in the same manner as the gRPC pseudo-Node does, and collect a (single)
/// response.
pub fn invoke_grpc_method<R, Q>(
    method_name: &str,
    req: &R,
    req_type_url: Option<&str>,
    invocation_channel: &crate::io::Sender<Invocation>,
) -> Result<Q>
where
    R: prost::Message,
    Q: prost::Message + Default,
{
    let rsp_receiver =
        invoke_grpc_method_stream(method_name, req, req_type_url, invocation_channel)?;
    // Read a single encapsulated response.
    let result = rsp_receiver.receive();
    rsp_receiver.close().expect("failed to close channel");
    let grpc_rsp = result.map_err(|status| {
        error!("failed to receive response: {:?}", status);
        build_status(
            rpc::Code::Internal,
            &format!("failed to receive gRPC response: {:?}", status),
        )
    })?;
    let (rsp, _last) = decap_response(grpc_rsp)?;

    Ok(rsp)
}

/// Generic function that handles request deserialization and response
/// serialization (and sending down a channel) for a function that handles a
/// request/response pair.
///
/// Panics if [de-]serialization or channel operations fail.
pub fn handle_req_rsp<C, R, Q>(mut node_fn: C, req: &[u8], mut writer: ChannelResponseWriter)
where
    C: FnMut(R) -> Result<Q>,
    R: prost::Message + Default,
    Q: prost::Message,
{
    let r = R::decode(req).expect("Failed to parse request protobuf message");
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
    R: prost::Message + Default,
{
    let r = R::decode(req).expect("Failed to parse request protobuf message");
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
    R: prost::Message + Default,
    Q: prost::Message + Default,
{
    // TODO(#97): better client-side streaming
    let rr = vec![R::decode(req).expect("Failed to parse request protobuf message")];
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
    R: prost::Message + Default,
{
    // TODO(#97): better client-side streaming
    let rr = vec![R::decode(req).expect("Failed to parse request protobuf message")];
    node_fn(rr, writer)
}

/// Default name for predefined Node configuration that corresponds to a gRPC pseudo-Node.
pub const DEFAULT_CONFIG_NAME: &str = "grpc_server";

/// Initialize a gRPC pseudo-Node with the default configuration.
pub fn init_default() {
    init(DEFAULT_CONFIG_NAME).unwrap();
}

/// Initializes a gRPC server pseudo-Node and passes it a handle to write invocations to.
///
/// Returns a [`ReadHandle`] to read invocations from.
///
/// [`ReadHandle`]: crate::ReadHandle
pub fn init(config: &str) -> std::result::Result<crate::ReadHandle, OakStatus> {
    // Create a channel and pass the read half to a new gRPC pseudo-Node.
    let (write_handle, read_handle) = crate::channel_create().expect("Couldn't create a channel");
    crate::node_create(config, "oak_main", read_handle)?;
    crate::channel_close(read_handle.handle).expect("Couldn't close a channel");

    // Create a separate channel for receiving invocations and pass it to a gRPC pseudo-Node.
    let (invocation_write_handle, invocation_read_handle) =
        crate::channel_create().expect("Couldn't create a channel");
    crate::channel_write(write_handle, &[], &[invocation_write_handle.handle])
        .expect("Couldn't write to a channel");

    Ok(invocation_read_handle)
}
