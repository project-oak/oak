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
        BoxedExtension, BoxedExtensionFactory, ExtensionFactory, OakApiNativeExtension, ABI_USIZE,
    },
};
use anyhow::Context;
use bytes::Bytes;
use oak_functions_abi::{
    proto::{ExtensionHandle, OakStatus},
    TfModelInferError, TfModelInferResponse,
};
use oak_functions_tf_inference::{parse_model, TensorFlowModel};
use prost::Message;
use std::{fs::File, io::Read, sync::Arc};
use wasmi::ValueType;

/// Host function name for invoking TensorFlow model inference.
const TF_ABI_FUNCTION_NAME: &str = "tf_model_infer";

// TODO(#2576): Move extension implementation to `tf_inference` crate once the Extension-related
// structs are in a separate crate.
impl OakApiNativeExtension for TensorFlowModel<Logger> {
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
            .expect("Fail to serialize tf response.");

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
        Ok(Box::new(model))
    }
}
