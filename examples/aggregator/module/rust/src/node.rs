//
// Copyright 2020 The Project Oak Authors
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

use std::fmt::Debug;
use crate::aggregation::{Aggregation, Monoid};
use log::{info, warn, error};
use oak::grpc;
// use oak::grpc::OakNode;
use crate::proto::aggregator::{GetAggregationResponse, SubmitSampleRequest};
use crate::proto::aggregator_grpc::{dispatch, Aggregator};
use protobuf::well_known_types::Empty;

impl<T: Monoid + Copy + Debug + Serializable> grpc::OakNode for Aggregation<T> {
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

pub trait Serializable {
    fn deserialize(data: Vec<u64>) -> Self;
    fn serialize(&self) -> Vec<u64>;
}

impl<T: Monoid + Copy + Debug + Serializable> Aggregator for Aggregation<T> {
    fn submit_sample(&mut self, req: SubmitSampleRequest) -> grpc::Result<Empty> {
        info!("Submit sample request: {:?}", req.values);
        if req.values.len() == T::len() {
            self.add(&T::deserialize(req.values));
            Ok(Empty::new())
        } else {
            error!("Wrong vector size: {:?}", req.values);
            Err(grpc::build_status(
                grpc::Code::INVALID_ARGUMENT,
                "Wrong vector size",
            ))
        }
    }

    fn get_aggregation(&mut self, _req: Empty) -> grpc::Result<GetAggregationResponse> {
        info!("Get aggregation request");
        let mut res = GetAggregationResponse::new();
        match self.get() {
            Some(values) => {
                info!("Aggregation: {:?}", values);
                res.values = values.serialize();
                Ok(res)
            }
            None => {
                warn!("Not enough samples have been aggregated");
                Ok(res)
            },
        }
    }
}
