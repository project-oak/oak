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
use crate::{proto, OakError};
use log::{error, warn};
pub use proto::grpc_encap::{GrpcRequest, GrpcResponse};
use protobuf::ProtobufEnum;

pub mod client;
mod invocation;
pub use invocation::Invocation;

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
    pub fn write<T: protobuf::Message>(
        &mut self,
        rsp: &T,
        mode: WriteMode,
    ) -> std::result::Result<(), OakError> {
        // Put the serialized response into a GrpcResponse message wrapper and
        // serialize it into the channel.
        let mut grpc_rsp = GrpcResponse::new();
        let mut any = protobuf::well_known_types::Any::new();
        rsp.write_to_writer(&mut any.value)?;
        grpc_rsp.set_rsp_msg(any);
        grpc_rsp.set_last(match mode {
            WriteMode::KeepOpen => false,
            WriteMode::Close => true,
        });
        self.sender.send(&grpc_rsp)?;
        if mode == WriteMode::Close {
            self.sender.close()?;
        }
        Ok(())
    }

    /// Write an empty gRPC response and optionally close out the method
    /// invocation. Any errors from the channel are silently dropped.
    pub fn write_empty(&mut self, mode: WriteMode) -> std::result::Result<(), OakError> {
        let mut grpc_rsp = GrpcResponse::new();
        grpc_rsp.set_rsp_msg(protobuf::well_known_types::Any::new());
        grpc_rsp.set_last(match mode {
            WriteMode::KeepOpen => false,
            WriteMode::Close => true,
        });
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
        let mut grpc_rsp = GrpcResponse::new();
        grpc_rsp.set_last(true);
        if let Err(status) = result {
            grpc_rsp.set_status(status);
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
            req.get_req_msg().value.as_slice(),
            ChannelResponseWriter::new(invocation.response_sender),
        );
        Ok(())
    }
}

/// Encapsulate a protocol buffer message in a GrpcRequest wrapper using the
/// given method name.
pub fn encap_request<T: protobuf::Message>(
    req: &T,
    req_type_url: Option<&str>,
    method_name: &str,
) -> Option<GrpcRequest> {
    // Put the request in a GrpcRequest wrapper and serialize it.
    let mut grpc_req = GrpcRequest::new();
    grpc_req.set_method_name(method_name.to_string());
    let mut any = protobuf::well_known_types::Any::new();
    if let Err(e) = req.write_to_writer(&mut any.value) {
        warn!("failed to serialize gRPC request: {}", e);
        return None;
    };
    if let Some(type_url) = req_type_url {
        any.set_type_url(type_url.to_string());
    }
    grpc_req.set_req_msg(any);
    grpc_req.set_last(true);
    Some(grpc_req)
}

/// Extract a protocol buffer message from a GrpcResponse wrapper.
/// Returns the message together with an indicator of whether this is the last
/// response.
pub fn decap_response<T: protobuf::Message>(mut grpc_rsp: GrpcResponse) -> Result<(T, bool)> {
    if grpc_rsp.get_status().get_code() != Code::OK.value() {
        return Err(grpc_rsp.take_status());
    }
    let rsp = protobuf::parse_from_bytes(&grpc_rsp.get_rsp_msg().value).map_err(|proto_err| {
        build_status(
            Code::INVALID_ARGUMENT,
            &format!("message parsing failed: {}", proto_err),
        )
    })?;
    Ok((rsp, grpc_rsp.get_last()))
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
    R: protobuf::Message,
{
    // Create a new channel for request message delivery.
    let (req_sender, req_receiver) =
        crate::io::channel_create::<GrpcRequest>().expect("failed to create channel");

    // Put the request in a GrpcRequest wrapper and send it into the request
    // message channel.
    let req =
        encap_request(req, req_type_url, method_name).expect("failed to serialize GrpcRequest");
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
    R: protobuf::Message,
    Q: protobuf::Message,
{
    let rsp_receiver =
        invoke_grpc_method_stream(method_name, req, req_type_url, invocation_channel)?;
    // Read a single encapsulated response.
    let result = rsp_receiver.receive();
    rsp_receiver.close().expect("failed to close channel");
    let grpc_rsp = result.map_err(|status| {
        error!("failed to receive response: {:?}", status);
        build_status(
            Code::INTERNAL,
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
