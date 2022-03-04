//
// Copyright 2022 The Project Oak Authors
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
use bytes::Bytes;
use log::Level;
use oak_functions_abi::proto::Inference;
use oak_logger::OakLogger;
use serde_derive::Deserialize;
use tract_tensorflow::prelude::{
    tract_ndarray::{ArrayBase, Dim, IxDynImpl, ViewRepr},
    *,
};

/// An optimized TypeModel with [`TypedFact`] and [`TypedOp`]. If optimization performed by `tract`
/// is not required, InferenceModel with [`InferenceFact`] and `InferenceOp` could be used
/// instead. These traits are available from the `tract-hir` crate.
///
/// More information: <https://github.com/sonos/tract/blob/main/doc/graph.md>
pub type Model = RunnableModel<TypedFact, Box<dyn TypedOp>, Graph<TypedFact, Box<dyn TypedOp>>>;

#[derive(Deserialize, Debug, Default)]
#[serde(deny_unknown_fields)]
pub struct TensorFlowModelConfig {
    /// Path to a TensorFlow model file.
    #[serde(default)]
    pub path: String,
    /// Shape of the input Tensors expected by the model.
    #[serde(default)]
    pub shape: Vec<u8>,
}

#[derive(Clone)]
pub struct TensorFlowModel<L: OakLogger + Clone> {
    model: Arc<Model>,
    shape: Vec<u8>,
    logger: L,
}

impl<L> TensorFlowModel<L>
where
    L: OakLogger + Clone,
{
    pub fn new(model: Arc<Model>, shape: Vec<u8>, logger: L) -> Self {
        Self {
            model,
            shape,
            logger,
        }
    }
    /// Run the model for the given input and return the resulting inference vector. Returns an
    /// error if the input vector does not have the desired shape, or the model fails to produce an
    /// inference.
    pub fn get_inference(&self, tensor_bytes: &[u8]) -> anyhow::Result<Inference> {
        let tensor_shape = self
            .shape
            .clone()
            .iter()
            .map(|&u| u.into())
            .collect::<Vec<usize>>();

        // Reshape the input, if the given shape matches the size of the given byte vector.
        let tensor = if (tensor_shape.iter().cloned().product::<usize>() * 4) == tensor_bytes.len()
        {
            unsafe {
                Tensor::from_raw::<f32>(&tensor_shape, tensor_bytes)
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
            .map(|item| {
                item.to_array_view::<f32>()
                    .context("could not map byte array to float")
            })
            .collect::<anyhow::Result<Vec<ArrayBase<ViewRepr<&f32>, Dim<IxDynImpl>>>>>()?
            .into_iter()
            .flatten()
            .cloned()
            .collect::<Vec<f32>>();

        Ok(Inference {
            shape,
            inference_vec,
        })
    }

    /// Logs an error message.
    ///
    /// The code assumes the message might contain sensitive information.
    pub fn log_error(&self, message: &str) {
        self.logger.log_sensitive(Level::Error, message)
    }
}

pub fn parse_model(bytes: Bytes, shape: &[u8]) -> anyhow::Result<Model> {
    use bytes::Buf;

    let dim = shape.iter().map(|&u| u.into()).collect::<Vec<i32>>();
    let mut reader = bytes.reader();

    // Creates the model based on the example in https://github.com/sonos/tract/tree/main/examples/tensorflow-mobilenet-v2
    tract_tensorflow::tensorflow()
        // load the model
        .model_for_read(&mut reader)?
        // specify input type and shape to be able to optimize the model
        .with_input_fact(0, InferenceFact::dt_shape(f32::datum_type(), dim))?
        // optimize the model
        .into_optimized()?
        // make the model runnable and fix its inputs and outputs
        .into_runnable()
}
