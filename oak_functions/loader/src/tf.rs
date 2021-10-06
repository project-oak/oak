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

use crate::{
    logger::Logger,
    server::{
        AbiPointer, AbiPointerOffset, BoxedExtension, ExtensionFactory, OakApiNativeExtension,
        WasmState, ABI_USIZE,
    },
};
use anyhow::Context;
use bytes::Bytes;
use log::Level;
use oak_functions_abi::proto::{Inference, OakStatus};
use prost::Message;
use serde_derive::Deserialize;
use std::{fs::File, io::Read};
use tract_tensorflow::prelude::{
    tract_ndarray::{ArrayBase, Dim, IxDynImpl, ViewRepr},
    *,
};
use wasmi::ValueType;

/// Host function name for invoking TensorFlow model inference.
const TF_ABI_FUNCTION_NAME: &str = "tf_model_infer";

/// An optimized TypeModel with [`TypedFact`] and [`TypedOp`]. If optimization performed by `tract`
/// is not required, InferenceModel with [`InferenceFact`] and [`InferenceOp`] could be used
/// instead. These traits are available from the `tract-hir` crate.
/// More information: https://github.com/sonos/tract/blob/main/doc/graph.md
type Model = RunnableModel<TypedFact, Box<dyn TypedOp>, Graph<TypedFact, Box<dyn TypedOp>>>;

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

struct TensorFlowModel {
    model: Arc<Model>,
    pub shape: Vec<u8>,
    logger: Logger,
}

impl TensorFlowModel {
    /// Run the model for the given input and return the resulting inference vector. Returns an
    /// error if the input vector does not have the desired shape, or the model fails to produce an
    /// inference.
    fn get_inference(
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
}

impl OakApiNativeExtension for TensorFlowModel {
    fn invoke(
        &mut self,
        wasm_state: &mut WasmState,
        args: wasmi::RuntimeArgs,
    ) -> Result<Result<(), OakStatus>, wasmi::Trap> {
        Ok(tf_model_infer(
            wasm_state,
            self,
            args.nth_checked(0)?,
            args.nth_checked(1)?,
            args.nth_checked(2)?,
            args.nth_checked(3)?,
        ))
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
}

/// Corresponds to the host ABI function [`tf_model_infer`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#tf_model_infer).    
fn tf_model_infer(
    wasm_state: &mut WasmState,
    tf_model: &TensorFlowModel,
    input_ptr: AbiPointer,
    input_len: AbiPointerOffset,
    inference_ptr_ptr: AbiPointer,
    inference_len_ptr: AbiPointer,
) -> Result<(), OakStatus> {
    let input = wasm_state
        .get_memory()
        .get(input_ptr, input_len as usize)
        .map_err(|err| {
            tf_model.logger.log_sensitive(
                Level::Error,
                &format!(
                    "tf_model_infer(): Unable to read input from guest memory: {:?}",
                    err
                ),
            );
            OakStatus::ErrInvalidArgs
        })?;

    let shape = tf_model
        .shape
        .clone()
        .iter()
        .cloned()
        .map(|u| u.into())
        .collect::<Vec<usize>>();

    // Get the inference, and convert it into a protobuf-encoded byte array
    let inference = tf_model.get_inference(&input, &shape).map_err(|err| {
        tf_model.logger.log_sensitive(
            Level::Error,
            &format!("tf_model_infer(): Unable to run inference: {:?}", err),
        );
        OakStatus::ErrBadTensorFlowModelInput
    })?;
    let mut encoded_inference = vec![];
    inference.encode(&mut encoded_inference).unwrap();

    let buf_ptr = wasm_state.alloc(encoded_inference.len() as u32);
    wasm_state.write_buffer_to_wasm_memory(&encoded_inference, buf_ptr)?;
    wasm_state.write_u32_to_wasm_memory(buf_ptr, inference_ptr_ptr)?;
    wasm_state.write_u32_to_wasm_memory(encoded_inference.len() as u32, inference_len_ptr)
}

/// Read a tensorFlow model from the given path, into a byte array.
pub async fn read_model_from_path(path: &str) -> anyhow::Result<Bytes> {
    let mut f = File::open(path).context("could not open TensorFlow model file")?;
    let mut buf = vec![];
    f.read_to_end(&mut buf)
        .context("could not read TensorFlow model from file")?;

    Ok(Bytes::from(buf))
}

pub struct TensorFlowFactory {
    model: Arc<Model>,
    pub shape: Vec<u8>,
    logger: Logger,
}

impl TensorFlowFactory {
    /// Creates an instance of TensorFlowFactory, by loading the model from the given byte array and
    /// optimizing it using the given shape.
    pub fn new(bytes: Bytes, shape: Vec<u8>, logger: Logger) -> anyhow::Result<Self> {
        use bytes::Buf;

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

        Ok(TensorFlowFactory {
            model: Arc::new(model),
            shape,
            logger,
        })
    }
}

impl ExtensionFactory for TensorFlowFactory {
    fn create(&self) -> anyhow::Result<BoxedExtension> {
        let model = TensorFlowModel {
            model: self.model.clone(),
            shape: self.shape.clone(),
            logger: self.logger.clone(),
        };

        Ok(Box::new(model))
    }
}
