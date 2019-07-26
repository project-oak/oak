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


use oak::GrpcResult;
use protobuf::Message;
use std::io::Write;

// Oak Node server interface
pub trait RunningAverageNode {
    fn submit_sample(&mut self, req: super::running_average::SubmitSampleRequest) -> GrpcResult<()>;

    fn get_average(&mut self) -> GrpcResult<super::running_average::GetAverageResponse>;
}

// Oak Node gRPC method dispatcher
pub fn dispatch(node: &mut dyn RunningAverageNode, method: &str, req: &[u8], out: &mut oak::SendChannelHalf) {
    match method {
        "/oak.examples.running_average.RunningAverage/SubmitSample" => {
            let r = protobuf::parse_from_bytes(&req).unwrap();
            node.submit_sample(r).unwrap();
        }
        "/oak.examples.running_average.RunningAverage/GetAverage" => {
            let mut result = oak::proto::grpc_encap::GrpcResponse::new();
            match node.get_average() {
                Ok(rsp) => {
                    let mut rsp_data = Vec::new();
                    rsp.write_to_writer(&mut rsp_data).unwrap();
                    result.set_rsp_msg(rsp_data);
                }
                Err(status) => result.set_status(status),
            }
            result.set_last(true);
            result.write_to_writer(out).unwrap();
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", method).unwrap();
            panic!("unknown method name");
        }
    };
}
