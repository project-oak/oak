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

// Oak node server interface
pub trait RunningAverageNode {
    fn submit_sample(&mut self, req: super::running_average::SubmitSampleRequest) -> GrpcResult<()>;

    fn get_average(&mut self) -> GrpcResult<super::running_average::GetAverageResponse>;
}

// Oak node gRPC method dispatcher
pub fn dispatch(node: &mut RunningAverageNode, grpc_method_name: &str, grpc_pair: &mut oak::ChannelPair) {
    match grpc_method_name {
        "/oak.examples.running_average.RunningAverage/SubmitSample" => {
            let req = protobuf::parse_from_reader(&mut grpc_pair.receive).unwrap();
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
