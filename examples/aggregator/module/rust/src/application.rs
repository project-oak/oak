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
use crate::proto::aggregator::Vector;
use crate::proto::aggregator_grpc::{dispatch, Aggregator};
use log::{info, warn};
use oak::grpc;
use protobuf::well_known_types::Empty;
use std::fmt::Debug;

pub trait Serializable<T> {
    fn deserialize(proto: &T) -> Self;
    fn serialize(&self) -> T;
}

/// Oak Application that collects aggregated data.
pub struct Application<T: Monoid> {
    aggregation: Aggregation<T>,
}

impl<T: Monoid> Application<T> {
    pub fn new(threshold: u64) -> Self {
        Application {
            aggregation: Aggregation::<T>::new(threshold),
        }
    }
}

impl<T> grpc::OakNode for Application<T>
where
    T: Monoid + Debug + Serializable<Vector>,
{
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

impl<T> Aggregator for Application<T>
where
    T: Monoid + Debug + Serializable<Vector>,
{
    fn submit_sample(&mut self, sample: Vector) -> grpc::Result<Empty> {
        info!("Submitted sample: {:?}", sample);
        self.aggregation.submit(&T::deserialize(&sample));
        Ok(Empty::new())
    }

    fn get_current_value(&mut self, _: Empty) -> grpc::Result<Vector> {
        info!("Get current value request");
        match self.aggregation.get() {
            Some(value) => {
                info!("Aggregated value: {:?}", value);
                Ok(value.serialize())
            }
            None => {
                warn!("Not enough samples have been aggregated");
                Err(grpc::build_status(
                    grpc::Code::PERMISSION_DENIED,
                    "Not enough samples have been aggregated",
                ))
            }
        }
    }
}
