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

use crate::extensions::OakApiNativeExtension;
use anyhow::Context;
use bytes::Bytes;
use oak_functions_abi::proto::Inference;
use std::{fs::File, io::Read};
#[cfg(feature = "oak-tf")]
use tract_tensorflow::prelude::{
    tract_ndarray::{ArrayBase, Dim, IxDynImpl, ViewRepr},
    *,
};
use prost::Message;

const TF_ABI_FUNCTION_NAME: &str = "tf_model_infer"

/// An optimized TypeModel with [`TypedFact`] and [`TypedOp`]. If optimization performed by `tract`
/// is not required, InferenceModel with [`InferenceFact`] and [`InferenceOp`] could be used
/// instead. These traits are available from the `tract-hir` crate.
/// More information: https://github.com/sonos/tract/blob/main/doc/graph.md
#[cfg(feature = "oak-tf")]
type Model = RunnableModel<TypedFact, Box<dyn TypedOp>, Graph<TypedFact, Box<dyn TypedOp>>>;

#[cfg(feature = "oak-tf")]
pub struct TensorFlowModel {
    model: Model,
    pub shape: Vec<u8>,
    index: usize,
}

#[cfg(feature = "oak-tf")]
impl TensorFlowModel {
    /// Creates an instance of TensorFlowModel, by loading the model from the given byte array and
    /// optimizing it using the given shape.
    pub fn create(bytes: Bytes, shape: Vec<u8>) -> anyhow::Result<Self> {
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
    fn invoke_index(
        &self,
        &mut wasm_state: WasmState,
        args: wasmi::RuntimeArgs,
    ) -> Option<Result<Option<wasmi::RuntimeValue>, wasmi::Trap>>{
        crate::server::map_host_errors(tf_model_infer(wasm_state, self,
            args.nth_checked(0)?,
            args.nth_checked(1)?,
            args.nth_checked(2)?,
            args.nth_checked(3)?,
        ))
    }

    // Similar to wasmi::ModuleImportResolver, but with additional optionality.
    fn resolve_func(&self) -> anyhow::Result<(usize, &wasmi::Signature)> {
        if self.index > 0 {
            Ok((
                self.index,
                wasmi::Signature::new(
                    &[
                        ABI_USIZE, // input_ptr
                        ABI_USIZE, // input_len
                        ABI_USIZE, // inference_ptr_ptr
                        ABI_USIZE, // inference_len_ptr
                    ][..],
                    Some(ValueType::I32),
                ),
            ))
        } else {
            anyhow::bail!("Index is not set for TensorFlowModel.");
        }
    }

    fn register_index(&mut self, index: usize) {
        self.index = index;
    }
}

/// Corresponds to the host ABI function [`tf_model_infer`](https://github.com/project-oak/oak/blob/main/docs/oak_functions_abi.md#tf_model_infer).    
fn tf_model_infer(
    &mut wasm_state: WasmState,
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
            wasm_state.logger.log_sensitive(
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
        wasm_state.logger.log_sensitive(
            Level::Error,
            &format!("tf_model_infer(): Unable to run inference: {:?}", err),
        );
        OakStatus::ErrBadTensorFlowModelInput
    })?;
    let mut encoded_inference = vec![];
    inference.encode(&mut encoded_inference).unwrap();

    let inference_ptr = wasm_state.alloc(encoded_inference.len() as u32);
    wasm_state.write_buffer_to_wasm_memory(&encoded_inference, inference_ptr)?;
    wasm_state.write_u32_to_wasm_memory(inference_ptr, inference_ptr_ptr)?;
    wasm_state.write_u32_to_wasm_memory(encoded_inference.len() as u32, inference_len_ptr)?;
    Ok(())
}

/// Read a tensorFlow model from the given path, into a byte array.
pub async fn read_model_from_path(path: &str) -> anyhow::Result<Bytes> {
    let mut f = File::open(path).context("could not open TensorFlow model file")?;
    let mut buf = vec![];
    f.read_to_end(&mut buf)
        .context("could not read TensorFlow model from file")?;

    Ok(Bytes::from(buf))
}

#[cfg(not(feature = "oak-tf"))]
pub struct TensorFlowModel;

#[cfg(not(feature = "oak-tf"))]
impl TensorFlowModel {
    pub fn create(_bytes: Bytes, _shape: Vec<u8>) -> anyhow::Result<Self> {
        anyhow::bail!("Unreachable: cannot create an instance of TensorFlowModel when `oak-tf` is not enabled")
    }
    pub fn get_inference(
        &self,
        _tensor_bytes: &[u8],
        _tensor_shape: &[usize],
    ) -> anyhow::Result<Inference> {
        anyhow::bail!("Unreachable: inference is not supported when `oak-tf` is not enabled")
    }
}
