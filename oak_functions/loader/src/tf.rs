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
use oak_functions_abi::proto::Inference;
use std::{fs::File, io::Read};
use tract_tensorflow::prelude::*;

/// An optimized TypeModel with [`TypedFact`] and [`TypedOp`]. If optimization performed by `tract`
/// is not required, InferenceModel with [`InferenceFact`] and [`InferenceOp`] could be used
/// instead. These traits are available from the `tract-hir` crate.
/// More information: https://github.com/sonos/tract/blob/main/doc/graph.md
type Model = RunnableModel<TypedFact, Box<dyn TypedOp>, Graph<TypedFact, Box<dyn TypedOp>>>;

pub struct TensorFlowModel {
    model: Model,
    pub shape: Vec<u8>,
}

impl TensorFlowModel {
    /// Creates an instance of TensorFlowModel, by loading the model from the given byte array and
    /// optimizing it using the given shape.
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
            // specify input type and shape to be able to optimize the model
            .with_input_fact(0, InferenceFact::dt_shape(f32::datum_type(), dim))?
            // optimize the model
            .into_optimized()?
            // make the model runnable and fix its inputs and outputs
            .into_runnable()?;

        Ok(TensorFlowModel { model, shape })
    }

    /// Run the model for the given input and return the resulting inference vector. Returns an
    /// error if the input vector does not have the desired shape, or the model fails to produce an
    /// inference.
    pub fn get_inference(
        &self,
        tensor_bytes: &[u8],
        tensor_shape: &[usize],
    ) -> anyhow::Result<Inference> {
        // Reshape the input, if the given shape matches the size of the given byte vector.
        let tensor = if (tensor_shape.iter().cloned().product::<usize>() * 4) == tensor_bytes.len()
        {
            unsafe {
                Tensor::from_raw::<f32>(tensor_shape, tensor_bytes)
                    .context("could not convert bytes into tensor")?
            }
        } else {
            anyhow::bail!("tensor bytes don't match the given shape");
        };

        // Get the inference
        let inference = self
            .model
            .run(tvec!(tensor))
            .context("could not get inference")?
            .into_vec();

        let mut shape = vec![inference.len() as u64];
        shape.append(&mut inference[0].shape().iter().map(|u| *u as u64).collect());
        let inference_vec = inference
            .iter()
            .flat_map(|item| item.to_array_view::<f32>().unwrap())
            .cloned()
            .collect::<Vec<f32>>();

        Ok(Inference {
            shape,
            inference_vec,
        })
    }
}

/// Read a tensorFlow model from the given path, into a byte array.
pub async fn read_model_from_path(path: &str) -> anyhow::Result<Bytes> {
    let mut f = File::open(path).context("could not open TensorFlow model file")?;
    let mut buf = vec![];
    f.read_to_end(&mut buf)
        .context("could not read TensorFlow model from file")?;

    Ok(Bytes::from(buf))
}
