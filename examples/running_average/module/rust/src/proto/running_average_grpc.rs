// This file is generated. Do not edit
// @generated

// https://github.com/Manishearth/rust-clippy/issues/702
#![allow(unknown_lints)]
#![allow(clippy)]

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


use oak::GrpcResult;
use protobuf::Message;
use std::io::Write;

// Oak Node server interface
pub trait RunningAverageNode {
    fn submit_sample(&mut self, req: super::running_average::SubmitSampleRequest) -> GrpcResult<()>;

    fn get_average(&mut self) -> GrpcResult<super::running_average::GetAverageResponse>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut RunningAverageNode, grpc_method_name: &str, grpc_pair: &mut oak::ChannelPair) {
    match grpc_method_name {
        "/oak.examples.running_average.RunningAverage/SubmitSample" => {
            // If the data fits in 256 bytes it will be read immediately.
            // If not, the vector will be resized and read on second attempt.
            let mut buf = Vec::<u8>::with_capacity(256);
            grpc_pair.receive.read_message(&mut buf).unwrap();
            let req = protobuf::parse_from_bytes(&buf).unwrap();
            node.submit_sample(req).unwrap();
        }
        "/oak.examples.running_average.RunningAverage/GetAverage" => {
            let rsp = node.get_average().unwrap();
            rsp.write_to_writer(&mut grpc_pair.send).unwrap();
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", grpc_method_name).unwrap();
            panic!("unknown method name");
        }
    };
}
