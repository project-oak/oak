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


use protobuf::Message;
use std::io::Write;

// Oak node server interface
pub trait RunningAverageNode {
    fn submit_sample(&mut self, req: super::running_average::SubmitSampleRequest);

    fn get_average(&mut self) -> super::running_average::GetAverageResponse;
}

// Oak node gRPC method dispatcher
pub fn dispatch(node: &mut RunningAverageNode, grpc_method_name: &str, grpc_in: &mut oak::ChannelHalf, grpc_out: &mut oak::ChannelHalf) {
    match grpc_method_name {
        "/oak.examples.running_average.RunningAverage/SubmitSample" => {
            let req = protobuf::parse_from_reader(grpc_in).unwrap();
            node.submit_sample(req);
        }
        "/oak.examples.running_average.RunningAverage/GetAverage" => {
            let rsp = node.get_average();
            rsp.write_to_writer(grpc_out).unwrap();
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", grpc_method_name).unwrap();
            panic!("unknown method name");
        }
    };
}
