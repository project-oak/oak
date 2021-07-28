//
// Copyright 2021 The Project Oak Authors
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
use bytes::{Buf, Bytes};
use hyper::{Body, Client, Request};
use hyper_rustls::HttpsConnector;
use oak_functions_abi::proto::Inference;
use tract_tensorflow::prelude::*;
type Model = RunnableModel<TypedFact, Box<dyn TypedOp>, Graph<TypedFact, Box<dyn TypedOp>>>;

pub struct TensorFlowModel {
    model: Model,
    pub shape: Vec<u8>,
}

impl TensorFlowModel {
    /// Creates an instance of TensorFlowModel, by loading the model in the specified path, and
    /// configuring it with the given shape.
    pub fn create(bytes: Bytes, shape: Vec<u8>) -> anyhow::Result<Self> {
        let dim = shape
            .iter()
            .cloned()
            .map(|u| u.into())
            .collect::<Vec<i32>>();
        let mut reader = bytes.reader();

        // Creates the model based on the example in https://github.com/sonos/tract/tree/main/examples/tensorflow-mobilenet-v2
        let model = tract_tensorflow::tensorflow()
            // load the model
            .model_for_read(&mut reader)?
            // specify input type and shape
            .with_input_fact(0, InferenceFact::dt_shape(f32::datum_type(), dim))?
            // optimize the model
            .into_optimized()?
            // make the model runnable and fix its inputs and outputs
            .into_runnable()?;

        Ok(TensorFlowModel { model, shape })
    }

    /// Run the model for the given input and return the resulting inference vector.
    pub fn get_inference(&self, tensor_bytes: &[u8], tensor_shape: &[usize]) -> Inference {
        // Reshape the input
        let tensor: Tensor =
            unsafe { Tensor::from_raw::<f32>(tensor_shape, tensor_bytes).unwrap() };

        // Get the inference
        let inference = self.model.run(tvec!(tensor)).unwrap().into_vec();
        let mut shape = vec![inference.len() as u64];
        shape.append(&mut inference[0].shape().iter().map(|u| *u as u64).collect());
        let inference_vec = inference
            .iter()
            .flat_map(|item| item.to_array_view::<f32>().unwrap())
            .cloned()
            .collect::<Vec<f32>>();

        Inference {
            shape,
            inference_vec,
        }
    }
}

/// Read the tensorFlow model from the given URL, into a byte array.
pub async fn read_model(url: &str) -> anyhow::Result<Bytes> {
    let https = HttpsConnector::with_native_roots();
    let client = Client::builder().build::<_, Body>(https);
    let request = Request::builder()
        .method(http::Method::GET)
        .uri(url)
        .body(Body::empty())
        .context("could not create request to read TensorFlow model")?;
    let response = client
        .request(request)
        .await
        .context("could not execute request to read TensorFlow model")?;

    match response.status() {
        http::StatusCode::OK => {
            let bytes = hyper::body::to_bytes(response.into_body())
                .await
                .context("could not read response body")?;
            Ok(bytes)
        }
        status => anyhow::bail!(
            "unexpected response with status `{}` from model server, ",
            status,
        ),
    }
}
