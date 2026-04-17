//
// Copyright 2025 The Project Oak Authors
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

use oak_proto_rust::oak::attestation::v1::{
    BinaryReferenceValue, KernelBinaryReferenceValue, OakContainersReferenceValues,
    OakRestrictedKernelReferenceValues, ReferenceValues, TextReferenceValue,
    binary_reference_value, kernel_binary_reference_value, reference_values, text_reference_value,
};
use prost::Message;

/// Shorthand to extract Oak Containers reference values as mutable.
pub fn get_oc_reference_values_mut(rvs: &mut ReferenceValues) -> &mut OakContainersReferenceValues {
    match rvs.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => oc,
        _ => panic!("no OC reference values"),
    }
}

/// Shorthand to extract Oak RK reference values as mutable.
pub fn get_rk_reference_values_mut(
    rvs: &mut ReferenceValues,
) -> &mut OakRestrictedKernelReferenceValues {
    match rvs.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakRestrictedKernel(rk) => rk,
        _ => panic!("no RK reference values"),
    }
}

pub fn manipulate_kernel_image(rv: Option<&mut KernelBinaryReferenceValue>) {
    if let Some(stripped) = rv {
        if let Some(kernel_binary_reference_value::Type::Digests(kernel_digests)) =
            &mut stripped.r#type
        {
            let d = kernel_digests.image.as_mut().expect("no kernel image");
            let raw = d.digests.as_mut_slice().first_mut().expect("no digest");
            if !raw.sha2_256.is_empty() {
                raw.sha2_256.as_mut_slice()[5] ^= 255;
            }
        }
    }
}

pub fn manipulate_kernel_setup_data(rv: Option<&mut KernelBinaryReferenceValue>) {
    if let Some(stripped) = rv {
        if let Some(kernel_binary_reference_value::Type::Digests(kernel_digests)) =
            &mut stripped.r#type
        {
            let d = kernel_digests.setup_data.as_mut().expect("no kernel setup data");
            let raw = d.digests.as_mut_slice().first_mut().expect("no digest");
            if !raw.sha2_256.is_empty() {
                raw.sha2_256.as_mut_slice()[5] ^= 255;
            }
        }
    }
}

pub fn manipulate_kernel_cmd_line(rv: Option<&mut TextReferenceValue>) {
    if let Some(stripped) = rv {
        match &mut stripped.r#type {
            Some(text_reference_value::Type::StringLiterals(strings)) => {
                strings.value.clear();
                strings.value.push("wrong".to_owned());
            }
            Some(text_reference_value::Type::Regex(regex)) => {
                regex.clear();
                regex.value = "wrong".to_owned();
            }
            _ => {}
        }
    }
}

pub fn manipulate_sha2_256(rv: Option<&mut BinaryReferenceValue>) {
    if let Some(stripped) = rv {
        if let Some(binary_reference_value::Type::Digests(d)) = &mut stripped.r#type {
            let raw = d.digests.as_mut_slice().first_mut().expect("no digest");
            if !raw.sha2_256.is_empty() {
                raw.sha2_256.as_mut_slice()[5] ^= 255;
            }
        }
    }
}

pub fn manipulate_sha2_384(rv: Option<&mut BinaryReferenceValue>) {
    if let Some(stripped) = rv {
        if let Some(binary_reference_value::Type::Digests(d)) = &mut stripped.r#type {
            let raw = d.digests.as_mut_slice().first_mut().expect("no digest");
            if !raw.sha2_384.is_empty() {
                raw.sha2_384.as_mut_slice()[5] ^= 255;
            }
        }
    }
}

pub fn get_stage0_rv(rvs: &mut ReferenceValues) -> Option<&mut BinaryReferenceValue> {
    match rvs.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => {
            oc.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap().stage0.as_mut()
        }
        reference_values::Type::OakRestrictedKernel(rk) => {
            rk.root_layer.as_mut().unwrap().amd_sev.as_mut().unwrap().stage0.as_mut()
        }
        _ => panic!("unexpected reference values"),
    }
}

pub fn get_kernel_rv(rvs: &mut ReferenceValues) -> Option<&mut KernelBinaryReferenceValue> {
    match rvs.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => {
            oc.kernel_layer.as_mut().unwrap().kernel.as_mut()
        }
        reference_values::Type::OakRestrictedKernel(rk) => {
            rk.kernel_layer.as_mut().unwrap().kernel.as_mut()
        }
        _ => panic!("unexpected reference values"),
    }
}

pub fn get_init_ram_fs_rv(rvs: &mut ReferenceValues) -> Option<&mut BinaryReferenceValue> {
    match rvs.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => {
            oc.kernel_layer.as_mut().unwrap().init_ram_fs.as_mut()
        }
        reference_values::Type::OakRestrictedKernel(rk) => {
            rk.kernel_layer.as_mut().unwrap().init_ram_fs.as_mut()
        }
        _ => panic!("unexpected reference values"),
    }
}

pub fn get_acpi_rv(rvs: &mut ReferenceValues) -> Option<&mut BinaryReferenceValue> {
    match rvs.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => {
            oc.kernel_layer.as_mut().unwrap().acpi.as_mut()
        }
        reference_values::Type::OakRestrictedKernel(rk) => {
            rk.kernel_layer.as_mut().unwrap().acpi.as_mut()
        }
        _ => panic!("unexpected reference values"),
    }
}

pub fn get_kernel_cmd_line_rv(rvs: &mut ReferenceValues) -> Option<&mut TextReferenceValue> {
    match rvs.r#type.as_mut().expect("no reference values") {
        reference_values::Type::OakContainers(oc) => {
            oc.kernel_layer.as_mut().unwrap().kernel_cmd_line_text.as_mut()
        }
        reference_values::Type::OakRestrictedKernel(rk) => {
            rk.kernel_layer.as_mut().unwrap().kernel_cmd_line_text.as_mut()
        }
        _ => panic!("unexpected reference values"),
    }
}

pub fn get_oc_system_image_rv(rvs: &mut ReferenceValues) -> Option<&mut BinaryReferenceValue> {
    let oc = get_oc_reference_values_mut(rvs);
    oc.system_layer.as_mut().unwrap().system_image.as_mut()
}

pub fn get_oc_container_rv(rvs: &mut ReferenceValues) -> Option<&mut BinaryReferenceValue> {
    let oc = get_oc_reference_values_mut(rvs);
    oc.container_layer.as_mut().unwrap().binary.as_mut()
}

pub fn get_oc_config_rv(rvs: &mut ReferenceValues) -> Option<&mut BinaryReferenceValue> {
    let oc = get_oc_reference_values_mut(rvs);
    oc.container_layer.as_mut().unwrap().configuration.as_mut()
}

pub fn get_rk_application_rv(rvs: &mut ReferenceValues) -> Option<&mut BinaryReferenceValue> {
    let rk = get_rk_reference_values_mut(rvs);
    rk.application_layer.as_mut().unwrap().binary.as_mut()
}

pub fn get_rk_config_rv(rvs: &mut ReferenceValues) -> Option<&mut BinaryReferenceValue> {
    let rk = get_rk_reference_values_mut(rvs);
    rk.application_layer.as_mut().unwrap().binary.as_mut()
}
