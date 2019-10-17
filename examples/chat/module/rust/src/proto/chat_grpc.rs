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
    fn create_room(&mut self, req: super::chat::CreateRoomRequest) -> grpc::Result<()>;

    fn destroy_room(&mut self, req: super::chat::DestroyRoomRequest) -> grpc::Result<()>;

    fn join_room(&mut self, req: super::chat::JoinRoomRequest, writer: grpc::ChannelResponseWriter);

    fn send_message(&mut self, req: super::chat::SentMessage) -> grpc::Result<()>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut dyn ChatNode, method: &str, req: &[u8], mut writer: grpc::ChannelResponseWriter) {
    match method {
        "/oak.examples.chat.Chat/CreateRoom" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            match node.create_room(r) {
                Ok(_) => writer.write_empty(grpc::WriteMode::Close),
                Err(status) => writer.close(Err(status)),
            }
        }
        "/oak.examples.chat.Chat/DestroyRoom" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            match node.destroy_room(r) {
                Ok(_) => writer.write_empty(grpc::WriteMode::Close),
                Err(status) => writer.close(Err(status)),
            }
        }
        "/oak.examples.chat.Chat/JoinRoom" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            node.join_room(r, writer)
        }
        "/oak.examples.chat.Chat/SendMessage" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            match node.send_message(r) {
                Ok(_) => writer.write_empty(grpc::WriteMode::Close),
                Err(status) => writer.close(Err(status)),
            }
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", method).unwrap();
            panic!("unknown method name");
        }
    };
}
