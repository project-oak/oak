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
        AbiPointer, AbiPointerOffset, BoxedExtension, BoxedExtensionFactory, ExtensionFactory,
        OakApiNativeExtension, WasmState, ABI_USIZE,
    },
};
use anyhow::Context;
use bytes::Bytes;
use oak_functions_abi::proto::OakStatus;
use oak_functions_tf_inference::{parse_model, TensorFlowModel};
use prost::Message;
use std::{fs::File, io::Read, sync::Arc};
use wasmi::ValueType;

/// Host function name for invoking TensorFlow model inference.
const TF_ABI_FUNCTION_NAME: &str = "tf_model_infer";

// TODO(#2576): Move extension implementation to `tf_inference` crate once the Extension-related
// structs are in a separate crate.
impl OakApiNativeExtension for TensorFlowModel<Logger> {
    fn invoke(
        &mut self,
        wasm_state: &mut WasmState,
        args: wasmi::RuntimeArgs,
    ) -> Result<Result<(), OakStatus>, wasmi::Trap> {
        let input_ptr: AbiPointer = args.nth_checked(0)?;
        let input_len: AbiPointerOffset = args.nth_checked(1)?;
        let inference_ptr_ptr: AbiPointer = args.nth_checked(2)?;
        let inference_len_ptr: AbiPointer = args.nth_checked(3)?;

        let extension_args = wasm_state
            .read_extension_args(input_ptr, input_len)
            .map_err(|err| {
                self.log_error(&format!(
                    "tf_model_infer(): Unable to read input from guest memory: {:?}",
                    err
                ));
                OakStatus::ErrInvalidArgs
            });

        let result = extension_args
            .and_then(|input| tf_model_infer(self, input))
            .and_then(|encoded_inference| {
                wasm_state.write_extension_result(
                    encoded_inference,
                    inference_ptr_ptr,
                    inference_len_ptr,
                )
            });

        Ok(result)
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
    tf_model: &TensorFlowModel<Logger>,
    input: Vec<u8>,
) -> Result<Vec<u8>, OakStatus> {
    // Get the inference, and convert it into a protobuf-encoded byte array
    let inference = tf_model.get_inference(&input).map_err(|err| {
        tf_model.log_error(&format!(
            "tf_model_infer(): Unable to run inference: {:?}",
            err
        ));
        OakStatus::ErrBadTensorFlowModelInput
    })?;
    Ok(inference.encode_to_vec())
}

/// Read a tensorFlow model from the given path, into a byte array.
pub fn read_model_from_path(path: &str) -> anyhow::Result<Bytes> {
    let mut f = File::open(path).context("could not open TensorFlow model file")?;
    let mut buf = vec![];
    f.read_to_end(&mut buf)
        .context("could not read TensorFlow model from file")?;

    Ok(Bytes::from(buf))
}

pub struct TensorFlowFactory {
    model: TensorFlowModel<Logger>,
}

impl TensorFlowFactory {
    /// Creates an instance of TensorFlowFactory, by loading the model from the given byte array and
    /// optimizing it using the given shape.
    pub fn new_boxed_extension_factory(
        bytes: Bytes,
        shape: Vec<u8>,
        logger: Logger,
    ) -> anyhow::Result<BoxedExtensionFactory> {
        let parsed_model = parse_model(bytes, &shape).context("couldn't parse model")?;
        let model = TensorFlowModel::new(Arc::new(parsed_model), shape, logger);
        Ok(Box::new(Self { model }))
    }
}

impl ExtensionFactory for TensorFlowFactory {
    fn create(&self) -> anyhow::Result<BoxedExtension> {
        let model = self.model.clone();
        Ok(BoxedExtension::Native(Box::new(model)))
    }
}
