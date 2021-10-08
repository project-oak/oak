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

use anyhow::Context;
use oak_abi::label::Label;
use prost::Message;
use tonic::{metadata::MetadataValue, service::interceptor::Interceptor, Request, Status};

/// Intercepts gRPC requests and adds the same `label` as a gRPC metadata.
#[derive(Clone)]
pub struct LabelInterceptor {
    /// Label that is being added to all gRPC requests.
    ///
    /// Is stored as a `Vec<u8>` because encoding a label may fail and `Into<Interceptor>` cannot
    /// return an error.
    label: Vec<u8>,
}

impl LabelInterceptor {
    pub fn create(label: &Label) -> anyhow::Result<Self> {
        let mut encoded_label = Vec::new();
        label
            .encode(&mut encoded_label)
            .context("Error encoding label")?;
        Ok(Self {
            label: encoded_label,
        })
    }
}

impl Interceptor for LabelInterceptor {
    fn call(&mut self, request: Request<()>) -> Result<Request<()>, Status> {
        let mut request = request;
        request.metadata_mut().insert_bin(
            oak_abi::OAK_LABEL_GRPC_METADATA_KEY,
            MetadataValue::from_bytes(self.label.as_ref()),
        );
        Ok(request)
    }
}
