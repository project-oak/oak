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
    binary_reference_value, endorsements, kernel_binary_reference_value, reference_values,
    text_reference_value, AmdSevReferenceValues, ApplicationLayerEndorsements,
    ApplicationLayerReferenceValues, BinaryReferenceValue, ContainerLayerReferenceValues,
    Endorsements, KernelBinaryReferenceValue, KernelLayerEndorsements, KernelLayerReferenceValues,
    OakContainersReferenceValues, OakRestrictedKernelEndorsements,
    OakRestrictedKernelReferenceValues, ReferenceValues, RootLayerEndorsements,
    RootLayerReferenceValues, SkipVerification, StringLiterals, SystemLayerReferenceValues,
    TcbVersion, TextReferenceValue,
};

use crate::endorsement_data::EndorsementData;

// Creates mock endorsements instance for a restricted kernel application.
pub fn create_rk_endorsements(vcek_cert: &[u8]) -> Endorsements {
    let root_layer = RootLayerEndorsements { tee_certificate: vcek_cert.to_vec(), stage0: None };
    let kernel_layer = KernelLayerEndorsements {
        kernel: None,
        kernel_cmd_line: None,
        init_ram_fs: None,
        memory_map: None,
        acpi: None,
    };
    let application_layer = ApplicationLayerEndorsements { binary: None, configuration: None };

    let ends = OakRestrictedKernelEndorsements {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        application_layer: Some(application_layer),
    };
    Endorsements {
        r#type: Some(endorsements::Type::OakRestrictedKernel(ends)),
        // TODO: b/375137648 - Populate `events` proto field.
        ..Default::default()
    }
}

// Creates trivial but valid reference values for an Oak Containers chain
// All endorsements are skipped with the exception of the one which happens
// to be available via `endorsement_data`.
pub fn create_oc_reference_values() -> ReferenceValues {
    let d = EndorsementData::load();
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };

    let amd_sev = AmdSevReferenceValues {
        min_tcb_version: Some(TcbVersion { boot_loader: 3, tee: 0, snp: 20, microcode: 209 }),
        allow_debug: false,
        stage0: Some(skip.clone()),
    };

    let root_layer = RootLayerReferenceValues { amd_sev: Some(amd_sev), ..Default::default() };
    let kernel_layer = KernelLayerReferenceValues {
        kernel: Some(KernelBinaryReferenceValue {
            r#type: Some(kernel_binary_reference_value::Type::Skip(SkipVerification {})),
        }),
        kernel_cmd_line_text: Some(TextReferenceValue {
            r#type: Some(text_reference_value::Type::StringLiterals(StringLiterals {
                value: vec![String::from(
                    "console=ttyS0 panic=-1 earlycon=uart,io,0x3F8 brd.rd_nr=1 brd.rd_size=3072000 brd.max_part=1 ip=10.0.2.15:::255.255.255.0::eth0:off net.ifnames=0 quiet",
                )],
            })),
        }),
        // The testdata endorsement happens to be oak_orchestrator.
        init_ram_fs: Some(BinaryReferenceValue {r#type: Some(binary_reference_value::Type::Endorsement(d.ref_value))}),
        memory_map: Some(skip.clone()),
        acpi: Some(skip.clone()),
    };
    let system_layer = SystemLayerReferenceValues { system_image: Some(skip.clone()) };
    let container_layer = ContainerLayerReferenceValues {
        binary: Some(skip.clone()),
        configuration: Some(skip.clone()),
    };
    let vs = OakContainersReferenceValues {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        system_layer: Some(system_layer),
        container_layer: Some(container_layer),
    };
    ReferenceValues { r#type: Some(reference_values::Type::OakContainers(vs)) }
}

// Creates trivial but valid reference values for a restricted kernel
// application. Almost all configurable checks are bypassed.
pub fn create_rk_reference_values() -> ReferenceValues {
    let skip = BinaryReferenceValue {
        r#type: Some(binary_reference_value::Type::Skip(SkipVerification {})),
    };

    let amd_sev = AmdSevReferenceValues {
        min_tcb_version: Some(TcbVersion { ..Default::default() }),
        allow_debug: false,
        stage0: Some(skip.clone()),
    };

    let root_layer = RootLayerReferenceValues { amd_sev: Some(amd_sev), ..Default::default() };
    #[allow(deprecated)]
    let kernel_layer = KernelLayerReferenceValues {
        kernel: Some(KernelBinaryReferenceValue {
            r#type: Some(kernel_binary_reference_value::Type::Skip(SkipVerification {})),
        }),
        kernel_cmd_line_text: Some(TextReferenceValue {
            r#type: Some(text_reference_value::Type::StringLiterals(StringLiterals {
                value: vec![String::from("console=ttyS0")],
            })),
        }),
        init_ram_fs: Some(skip.clone()),
        memory_map: Some(skip.clone()),
        acpi: Some(skip.clone()),
    };
    let application_layer = ApplicationLayerReferenceValues {
        binary: Some(skip.clone()),
        configuration: Some(skip.clone()),
    };
    let vs = OakRestrictedKernelReferenceValues {
        root_layer: Some(root_layer),
        kernel_layer: Some(kernel_layer),
        application_layer: Some(application_layer),
    };
    ReferenceValues { r#type: Some(reference_values::Type::OakRestrictedKernel(vs)) }
}
