// This file is generated. Do not edit
// @generated

// https://github.com/rust-lang/rust-clippy/issues/702
#![allow(unknown_lints)]
#![allow(clippy::all)]

#![cfg_attr(rustfmt, rustfmt_skip)]

#![allow(box_pointers)]
#![allow(dead_code)]
#![allow(missing_docs)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(trivial_casts)]
#![allow(unsafe_code)]
#![allow(unused_imports)]
#![allow(unused_results)]


use oak::grpc;
use protobuf::Message;
use std::io::Write;

// Oak Node server interface
pub trait Chat {
    fn create_room(&mut self, req: super::chat::CreateRoomRequest) -> grpc::Result<protobuf::well_known_types::Empty>;
    fn destroy_room(&mut self, req: super::chat::DestroyRoomRequest) -> grpc::Result<protobuf::well_known_types::Empty>;
    fn subscribe(&mut self, req: super::chat::SubscribeRequest, writer: grpc::ChannelResponseWriter);
    fn send_message(&mut self, req: super::chat::SendMessageRequest) -> grpc::Result<protobuf::well_known_types::Empty>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch<T: Chat>(node: &mut T, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
    match method {
        "/oak.examples.chat.Chat/CreateRoom" => grpc::handle_req_rsp(|r| node.create_room(r), req, writer),
        "/oak.examples.chat.Chat/DestroyRoom" => grpc::handle_req_rsp(|r| node.destroy_room(r), req, writer),
        "/oak.examples.chat.Chat/Subscribe" => grpc::handle_req_stream(|r, w| node.subscribe(r, w), req, writer),
        "/oak.examples.chat.Chat/SendMessage" => grpc::handle_req_rsp(|r| node.send_message(r), req, writer),
        _ => {
            panic!("unknown method name: {}", method);
        }
    };
}

// Client interface
pub struct ChatClient(pub oak::grpc::client::Client);

impl ChatClient {
    pub fn create_room(&self, req: super::chat::CreateRoomRequest) -> grpc::Result<protobuf::well_known_types::Empty> {
        oak::grpc::invoke_grpc_method("/oak.examples.chat.Chat/CreateRoom", req, &self.0.invocation_sender)
    }
    pub fn destroy_room(&self, req: super::chat::DestroyRoomRequest) -> grpc::Result<protobuf::well_known_types::Empty> {
        oak::grpc::invoke_grpc_method("/oak.examples.chat.Chat/DestroyRoom", req, &self.0.invocation_sender)
    }
    pub fn subscribe(&self, req: super::chat::SubscribeRequest) -> grpc::Result<oak::io::Receiver<grpc::GrpcResponse>> {
        oak::grpc::invoke_grpc_method_stream("/oak.examples.chat.Chat/Subscribe", req, &self.0.invocation_sender)
    }
    pub fn send_message(&self, req: super::chat::SendMessageRequest) -> grpc::Result<protobuf::well_known_types::Empty> {
        oak::grpc::invoke_grpc_method("/oak.examples.chat.Chat/SendMessage", req, &self.0.invocation_sender)
    }
}
