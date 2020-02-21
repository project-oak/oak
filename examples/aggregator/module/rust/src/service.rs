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

use crate::aggregation::{Aggregation, Monoid};
use crate::proto::aggregator::{GetAggregationResponse, SubmitSampleRequest};
use crate::proto::aggregator_grpc::{dispatch, Aggregator};
use log::{info, warn};
use oak::grpc;
use protobuf::well_known_types::Empty;
use std::fmt::Debug;

pub trait Serializable {
    fn deserialize(data: Vec<u64>) -> Self;
    fn serialize(&self) -> Vec<u64>;
}

impl<T> grpc::OakNode for Aggregation<T>
where
    T: Monoid + Clone + Debug + Serializable,
{
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

impl<T> Aggregator for Aggregation<T>
where
    T: Monoid + Clone + Debug + Serializable,
{
    fn submit_sample(&mut self, req: SubmitSampleRequest) -> grpc::Result<Empty> {
        info!("Submit sample request: {:?}", req.values);
        self.add(&T::deserialize(req.values));
        Ok(Empty::new())
    }

    fn get_aggregation(&mut self, _req: Empty) -> grpc::Result<GetAggregationResponse> {
        info!("Get aggregation request");
        let mut res = GetAggregationResponse::new();
        match self.get() {
            Some(values) => {
                info!("Aggregation: {:?}", values);
                res.success = true;
                res.values = values.serialize();
            }
            None => {
                warn!("Not enough samples have been aggregated");
                res.success = false;
            }
        };
        Ok(res)
    }
}
