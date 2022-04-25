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

use std::{fs::File, io::Read, sync::Arc};

use anyhow::Context;
use bytes::Bytes;
use log::Level;
use oak_functions_abi::{
    proto::{Inference, OakStatus},
    ExtensionHandle, TfModelInferError, TfModelInferResponse,
};
use oak_functions_extension::{ExtensionFactory, OakApiNativeExtension};
use oak_logger::OakLogger;
use prost::Message;
use serde_derive::Deserialize;
use tract_tensorflow::prelude::{
    tract_ndarray::{ArrayBase, Dim, IxDynImpl, ViewRepr},
    *,
};
use wasmi::ValueType;

// TODO(#2752): Remove once we call all extensions with invoke.
const ABI_USIZE: ValueType = ValueType::I32;

/// Host function name for invoking TensorFlow model inference.
const TF_ABI_FUNCTION_NAME: &str = "tf_model_infer";

impl<L: OakLogger> OakApiNativeExtension for TensorFlowModel<L> {
    fn invoke(&mut self, request: Vec<u8>) -> Result<Vec<u8>, OakStatus> {
        let inference = self.get_inference(&request).map_err(|err| {
            self.log_error(&format!(
                "tf_model_infer(): Unable to run inference: {:?}",
                err
            ));
            TfModelInferError::BadTensorFlowModelInput
        });
        let result = inference.map(|inference| inference.encode_to_vec());
        let response = bincode::serialize(&TfModelInferResponse { result })
            .expect("Failed to serialize TF response.");

        Ok(response)
    }

    /// Each Oak Functions application can have at most one instance of TensorFlowModule. So it is
    /// fine to return a constant name in the metadata.
    fn get_metadata(&self) -> (String, wasmi::Signature) {
        let signature = wasmi::Signature::new(
            &[
                ABI_USIZE, // input_ptr
                ABI_USIZE, // input_len
                ABI_USIZE, // inference_ptr_ptr
                ABI_USIZE, // inference_len_ptr
            ][..],
            Some(ValueType::I32),
        );

        (TF_ABI_FUNCTION_NAME.to_string(), signature)
    }

    fn terminate(&mut self) -> anyhow::Result<()> {
        Ok(())
    }

    fn get_handle(&self) -> ExtensionHandle {
        ExtensionHandle::TfHandle
    }
}

/// Read a tensorFlow model from the given path, into a byte array.
pub fn read_model_from_path(path: &str) -> anyhow::Result<Bytes> {
    // TODO(#2753): Read config in loader.
    let mut f = File::open(path).context("could not open TensorFlow model file")?;
    let mut buf = vec![];
    f.read_to_end(&mut buf)
        .context("could not read TensorFlow model from file")?;

    Ok(Bytes::from(buf))
}

pub struct TensorFlowFactory<L: OakLogger> {
    model: TensorFlowModel<L>,
}

impl<L> TensorFlowFactory<L>
where
    L: OakLogger + 'static,
{
    /// Creates an instance of TensorFlowFactory, by loading the model from the given byte array and
    /// optimizing it using the given shape.
    pub fn new_boxed_extension_factory(
        bytes: Bytes,
        shape: Vec<u8>,
        logger: L,
    ) -> anyhow::Result<Box<dyn ExtensionFactory<L>>> {
        let parsed_model = parse_model(bytes, &shape).context("couldn't parse model")?;
        let model = TensorFlowModel::new(Arc::new(parsed_model), shape, logger);
        Ok(Box::new(Self { model }))
    }
}

impl<L> ExtensionFactory<L> for TensorFlowFactory<L>
where
    L: OakLogger + 'static,
{
    fn create(&self) -> anyhow::Result<Box<dyn OakApiNativeExtension>> {
        let model = self.model.clone();
        Ok(Box::new(model))
    }
}

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
pub struct TensorFlowModel<L: OakLogger> {
    model: Arc<Model>,
    shape: Vec<u8>,
    logger: L,
}

impl<L: OakLogger> TensorFlowModel<L> {
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
