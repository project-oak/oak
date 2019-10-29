// This file is generated. Do not edit
// @generated

// https://github.com/Manishearth/rust-clippy/issues/702
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
pub trait ChatNode {
    fn create_room(&mut self, req: super::chat::CreateRoomRequest) -> grpc::Result<protobuf::well_known_types::Empty>;
    fn destroy_room(&mut self, req: super::chat::DestroyRoomRequest) -> grpc::Result<protobuf::well_known_types::Empty>;
    fn join_room(&mut self, req: super::chat::JoinRoomRequest, writer: grpc::ChannelResponseWriter);
    fn send_message(&mut self, req: super::chat::SentMessage) -> grpc::Result<protobuf::well_known_types::Empty>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut dyn ChatNode, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
    match method {
        "/oak.examples.chat.Chat/CreateRoom" => grpc::handle_req_rsp(|r| node.create_room(r), req, writer),
        "/oak.examples.chat.Chat/DestroyRoom" => grpc::handle_req_rsp(|r| node.destroy_room(r), req, writer),
        "/oak.examples.chat.Chat/JoinRoom" => grpc::handle_req_stream(|r, w| node.join_room(r, w), req, writer),
        "/oak.examples.chat.Chat/SendMessage" => grpc::handle_req_rsp(|r| node.send_message(r), req, writer),
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", method).unwrap();
            panic!("unknown method name");
        }
    };
}
