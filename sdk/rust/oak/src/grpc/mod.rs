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

use crate::{
    io::{ReceiverExt, SenderExt},
    OakError, OakStatus,
};
use anyhow::Context;
use log::{error, warn};
use oak_abi::label::Label;
use oak_services::proto::google::rpc;
pub use oak_services::proto::{
    google::rpc::*,
    oak::encap::{GrpcRequest, GrpcResponse},
};

pub mod client;
pub mod server;

/// Result type that uses a [`Status`] type for error values.
///
/// [`Status`]: oak_services::proto::google::rpc::Status
pub type Result<T> = std::result::Result<T, rpc::Status>;
pub type Invocation = crate::proto::oak::invocation::GrpcInvocation;

impl Invocation {
    pub fn close(self) -> anyhow::Result<()> {
        self.receiver
            .expect("Couldn't get receiver")
            .close()
            .context("Couldn't close the receiver")?;
        self.sender
            .expect("Couldn't get sender")
            .close()
            .context("Couldn't close the sender")
    }
}

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
        &self,
        rsp: &T,
        mode: WriteMode,
    ) -> std::result::Result<(), OakError> {
        // Put the serialized response into a GrpcResponse message wrapper and
        // serialize it into the channel.
        let mut bytes = Vec::new();
        rsp.encode(&mut bytes)?;
        let grpc_rsp = GrpcResponse {
            rsp_msg: bytes,
            status: None,
            last: match mode {
                WriteMode::KeepOpen => false,
                WriteMode::Close => true,
            },
        };
        // TODO(#1739): Do not automatically use privilege.
        self.sender.send_with_downgrade(&grpc_rsp)?;
        if mode == WriteMode::Close {
            self.sender.close()?;
        }
        Ok(())
    }

    /// Write an empty gRPC response and optionally close out the method
    /// invocation. Any errors from the channel are silently dropped.
    pub fn write_empty(&self, mode: WriteMode) -> std::result::Result<(), OakError> {
        let grpc_rsp = GrpcResponse {
            rsp_msg: Vec::new(),
            status: None,
            last: match mode {
                WriteMode::KeepOpen => false,
                WriteMode::Close => true,
            },
        };
        // TODO(#1739): Do not automatically use privilege.
        self.sender.send_with_downgrade(&grpc_rsp)?;
        if mode == WriteMode::Close {
            self.sender.close()?;
        }
        Ok(())
    }

    /// Close out the gRPC method invocation with the given final result.
    pub fn close(&self, result: Result<()>) -> std::result::Result<(), OakError> {
        // Build a final GrpcResponse message wrapper and serialize it into the
        // channel.
        let mut grpc_rsp = GrpcResponse {
            last: true,
            ..Default::default()
        };
        if let Err(status) = result {
            grpc_rsp.status = Some(status);
        }
        // TODO(#1739): Do not automatically use privilege.
        self.sender.send_with_downgrade(&grpc_rsp)?;
        self.sender.close()?;
        Ok(())
    }
}

/// Trait for Oak Nodes that act as a gRPC services.
///
/// A `ServerNode` instance is normally passed to [`oak::run_command_loop`], to
/// allow repeated invocation of its `invoke()` method.
///
/// You can choose to implement this trait yourself, or use the convenient
/// `Dispatcher` created by the gRPC code generator.
///
/// [`oak::run_command_loop`]: ../../oak/fn.run_command_loop.html
pub trait ServerNode {
    /// Process a single gRPC method invocation.
    ///
    /// The method name is provided by `method` and the incoming serialized gRPC
    /// request is held in `req`.  Response messages should be written using
    /// `writer.write`, followed by `writer.close`.
    fn invoke(&mut self, method: &str, req: &[u8], writer: ChannelResponseWriter);
}

impl<T: ServerNode> crate::CommandHandler for T {
    type Command = Invocation;
    /// Handle incoming gRPC events for a [`ServerNode`].
    ///
    /// Invoking the given `node`'s [`invoke`] method for each incoming request that
    /// arrives on the inbound channel as a serialized [`Invocation`] object,
    /// giving the [`invoke`] method the outbound channel for encapsulated responses
    /// to be written to.
    ///
    /// [`invoke`]: ServerNode::invoke
    fn handle_command(&mut self, invocation: Invocation) -> anyhow::Result<()> {
        let response_writer = ChannelResponseWriter::new(
            invocation
                .sender
                .ok_or(OakError::OakStatus(OakStatus::ErrBadHandle))?,
        );

        let request_receiver = invocation
            .receiver
            .ok_or(OakError::OakStatus(OakStatus::ErrBadHandle))?;
        // Read a single encapsulated request message from the read half.
        let req: GrpcRequest = request_receiver.receive().map_err(|err| {
            // TODO(#1078): If it's clear that the issue is caused by a too restrictive label
            // (permission denied), then return a more specific error to the gRPC client.
            warn!(
                "could not receive gRPC request from gRPC invocation: {}",
                err
            );
            // If anything fails while reading the gRPC request, then at least try to send a
            // gRPC error response back to the gRPC client, rather than just returning from this
            // method with `?`, since otherwise that would leave the gRPC client hanging
            // forever.
            // If sending this gRPC request also fails, we just log the error here and discard
            // it, but we still return the original error to the caller of this
            // function.
            if let Err(err) = response_writer.close(Result::Err(build_status(
                rpc::Code::InvalidArgument,
                "could not process gRPC request",
            ))) {
                warn!(
                    "could not send gRPC error back to gRPC client through gRPC invocation: {}",
                    err
                );
            };
            err
        })?;

        // Since we are expecting a single message, close the channel immediately.
        // This will change when we implement client streaming (#97).
        request_receiver.close()?;
        // TODO(#97): Implement client streaming.
        assert!(
            req.last,
            "Support for streaming requests not yet implemented"
        );
        self.invoke(&req.method_name, req.req_msg.as_slice(), response_writer);
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
    let rsp = T::decode(grpc_rsp.rsp_msg.as_slice()).map_err(|proto_err| {
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
    invocation_channel: &crate::io::Sender<Invocation>,
) -> Result<crate::io::Receiver<GrpcResponse>>
where
    R: prost::Message,
{
    // Create a new channel for request message delivery.
    // TODO(#1739): Don't use privilege automatically.
    let (req_sender, req_receiver) = crate::io::channel_create_with_downgrade::<GrpcRequest>(
        "gRPC request",
        &Label::public_untrusted(),
    )
    .expect("failed to create channel");

    // Put the request in a GrpcRequest wrapper and send it into the request
    // message channel.
    let req = oak_services::grpc::encap_request(req, method_name)
        .expect("failed to serialize GrpcRequest");
    // TODO(#1739): Don't use privilege automatically.
    req_sender
        .send_with_downgrade(&req)
        .expect("failed to write to channel");
    req_sender.close().expect("failed to close channel");

    // Create a new channel for responses to arrive on.
    // TODO(#1739): Don't use privilege automatically.
    let (rsp_sender, rsp_receiver) = crate::io::channel_create_with_downgrade::<GrpcResponse>(
        "gRPC response",
        &Label::public_untrusted(),
    )
    .expect("failed to create channel");

    // Build an Invocation holding the two channels and send it down the
    // specified channel.
    let invocation = Invocation {
        receiver: Some(req_receiver.clone()),
        sender: Some(rsp_sender.clone()),
    };

    // TODO(#1739): Don't use privilege automatically.
    invocation_channel
        .send_with_downgrade(&invocation)
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
    invocation_channel: &crate::io::Sender<Invocation>,
) -> Result<Q>
where
    R: prost::Message,
    Q: prost::Message + Default,
{
    let rsp_receiver = invoke_grpc_method_stream(method_name, req, invocation_channel)?;
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

/// Trait implemented by all server method variants, applied to a server receiver instance having
/// concrete type `T`.
pub trait Invocable<T> {
    /// Generic function that handles request deserialization and response serialization (and
    /// sending down a channel) for a function that handles a request / response pair (either unary
    /// or streaming).
    ///
    /// Panics if [de-]serialization or channel operations fail.
    fn invoke(&self, target: &mut T, req: &[u8], writer: ChannelResponseWriter);
}

/// Enum with variants for all combinations of {request, response} × {unary , streaming}, each
/// containing a pointer to the function of the appropriate type defined on a service
/// implementation.
///
/// The functions are "uncurried", i.e. they include an explicit parameter for the receiver type,
/// which corresponds to `self` in the method definition.
///
/// Note that the variants with response stream do not make use of the type parameter `Q`, so this
/// must be manually specified when creating one of those instances if the compiler cannot infer it
/// from the context.
pub enum ServerMethod<T, R, Q> {
    UnaryUnary(fn(&mut T, R) -> Result<Q>),
    UnaryStream(fn(&mut T, R, ChannelResponseWriter)),
    StreamUnary(fn(&mut T, Vec<R>) -> Result<Q>),
    StreamStream(fn(&mut T, Vec<R>, ChannelResponseWriter)),
}

impl<T, R, Q> Invocable<T> for ServerMethod<T, R, Q>
where
    R: prost::Message + Default,
    Q: prost::Message,
{
    fn invoke(&self, target: &mut T, req: &[u8], writer: ChannelResponseWriter) {
        match self {
            ServerMethod::UnaryUnary(server_method) => {
                let r = R::decode(req).expect("Failed to parse request protobuf message");
                let result = match server_method(target, r) {
                    Ok(rsp) => writer.write(&rsp, WriteMode::Close),
                    Err(status) => writer.close(Err(status)),
                };
                if let Err(e) = result {
                    panic!("Failed to process response: {:?}", e)
                }
            }
            ServerMethod::UnaryStream(server_method) => {
                let r = R::decode(req).expect("Failed to parse request protobuf message");
                server_method(target, r, writer)
            }
            ServerMethod::StreamUnary(server_method) => {
                // TODO(#97): better client-side streaming
                let rr = vec![R::decode(req).expect("Failed to parse request protobuf message")];
                let result = match server_method(target, rr) {
                    Ok(rsp) => writer.write(&rsp, WriteMode::Close),
                    Err(status) => writer.close(Err(status)),
                };
                if let Err(e) = result {
                    panic!("Failed to process response: {:?}", e)
                }
            }
            ServerMethod::StreamStream(server_method) => {
                // TODO(#97): better client-side streaming
                let rr = vec![R::decode(req).expect("Failed to parse request protobuf message")];
                server_method(target, rr, writer)
            }
        }
    }
}

/// Implements the [`ServerNode`] trait for the specified type using the provided dispatcher, which
/// is generated by the `oak_util` crate from the protobuf service definition.
///
/// ```ignore
/// #[derive(Default)]
/// struct Handler;
///
/// oak::impl_dispatcher!(impl Handler : ServiceDispatcher);
/// ```
#[macro_export]
macro_rules! impl_dispatcher {
    (impl $handler:ty : $dispatcher:ty) => {
        impl ::oak::grpc::ServerNode for $handler {
            fn invoke(
                &mut self,
                method_name: &str,
                req: &[u8],
                writer: ::oak::grpc::ChannelResponseWriter,
            ) {
                match <$dispatcher>::server_method(method_name) {
                    Some(server_method) => server_method.invoke(self, req, writer),
                    None => ::log::error!("unknown method name: {}", method_name),
                }
            }
        }
    };
}
