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

use prost::Message;

use crate::oak::{
    Variant,
    attestation::v1::{
        AmdSevSnpEndorsement, ApplicationEndorsement, ConfidentialSpaceEndorsement,
        ContainerEndorsement, FirmwareEndorsement, KernelEndorsement,
        SessionBindingPublicKeyEndorsement, SystemEndorsement,
    },
};

impl Variant {
    pub fn is_empty(&self) -> bool {
        self.id.is_empty()
    }
}

impl From<Option<Variant>> for Variant {
    fn from(value: Option<Variant>) -> Self {
        value.unwrap_or_default()
    }
}

/// A random ID for each endorsement protocol buffer type that appears as ID
/// in the oak::Variant encoding.
const AMD_SEV_SNP_PLATFORM_ENDORSEMENT_ID: [u8; 16] =
    [90, 18, 208, 15, 72, 160, 66, 36, 191, 244, 151, 92, 118, 87, 67, 143];
const FIRMWARE_ENDORSEMENT_ID: [u8; 16] =
    [222, 74, 13, 85, 96, 234, 77, 198, 171, 209, 9, 237, 116, 79, 128, 234];
const KERNEL_ENDORSEMENT_ID: [u8; 16] =
    [137, 81, 29, 101, 93, 53, 70, 1, 144, 11, 30, 109, 186, 248, 66, 182];
const SYSTEM_ENDORSEMENT_ID: [u8; 16] =
    [71, 34, 101, 93, 150, 61, 79, 201, 132, 67, 241, 69, 113, 221, 50, 162];
const APPLICATION_ENDORSEMENT_ID: [u8; 16] =
    [232, 78, 215, 20, 102, 157, 67, 10, 166, 15, 138, 101, 30, 90, 85, 3];
const CONTAINER_ENDORSEMENT_ID: [u8; 16] =
    [114, 151, 165, 31, 160, 93, 73, 161, 175, 219, 100, 205, 238, 7, 134, 45];
const SESSION_BINDING_PUBLIC_KEY_ENDORSEMENT_ID: [u8; 16] =
    [39, 60, 254, 29, 91, 201, 76, 245, 181, 200, 107, 195, 252, 140, 230, 166];
const CONFIDENTIAL_SPACE_ENDORSEMENT_ID: [u8; 16] =
    [101, 107, 31, 55, 118, 106, 162, 143, 49, 81, 224, 1, 135, 123, 189, 122];

fn try_into_message<M: Message + Default>(id: &[u8], variant: &Variant) -> Result<M, &'static str> {
    if variant.id != id {
        return Err("unexpected variant ID");
    }

    M::decode(variant.value.as_ref()).map_err(|_| "couldn't decode variant")
}

impl TryFrom<&Variant> for AmdSevSnpEndorsement {
    type Error = &'static str;
    fn try_from(value: &Variant) -> Result<Self, Self::Error> {
        try_into_message(&AMD_SEV_SNP_PLATFORM_ENDORSEMENT_ID, value)
    }
}

impl TryFrom<&Variant> for FirmwareEndorsement {
    type Error = &'static str;
    fn try_from(value: &Variant) -> Result<Self, Self::Error> {
        try_into_message(&FIRMWARE_ENDORSEMENT_ID, value)
    }
}

impl TryFrom<&Variant> for KernelEndorsement {
    type Error = &'static str;
    fn try_from(value: &Variant) -> Result<Self, Self::Error> {
        try_into_message(&KERNEL_ENDORSEMENT_ID, value)
    }
}

impl TryFrom<&Variant> for SystemEndorsement {
    type Error = &'static str;
    fn try_from(value: &Variant) -> Result<Self, Self::Error> {
        try_into_message(&SYSTEM_ENDORSEMENT_ID, value)
    }
}

impl TryFrom<&Variant> for ContainerEndorsement {
    type Error = &'static str;
    fn try_from(value: &Variant) -> Result<Self, Self::Error> {
        try_into_message(&CONTAINER_ENDORSEMENT_ID, value)
    }
}

impl TryFrom<&Variant> for ApplicationEndorsement {
    type Error = &'static str;
    fn try_from(value: &Variant) -> Result<Self, Self::Error> {
        try_into_message(&APPLICATION_ENDORSEMENT_ID, value)
    }
}

impl TryFrom<&Variant> for SessionBindingPublicKeyEndorsement {
    type Error = &'static str;
    fn try_from(value: &Variant) -> Result<Self, Self::Error> {
        try_into_message(&SESSION_BINDING_PUBLIC_KEY_ENDORSEMENT_ID, value)
    }
}

impl TryFrom<&Variant> for ConfidentialSpaceEndorsement {
    type Error = &'static str;
    fn try_from(value: &Variant) -> Result<Self, Self::Error> {
        try_into_message(&CONFIDENTIAL_SPACE_ENDORSEMENT_ID, value)
    }
}

macro_rules! impl_try_from_variant_to_option {
    ($value_type:ty) => {
        impl TryFrom<&Variant> for Option<$value_type> {
            type Error = &'static str;
            fn try_from(value: &Variant) -> Result<Self, Self::Error> {
                let result = if !value.is_empty() { Some(value.try_into()?) } else { None };
                Ok(result)
            }
        }
    };
}

impl_try_from_variant_to_option!(AmdSevSnpEndorsement);
impl_try_from_variant_to_option!(FirmwareEndorsement);
impl_try_from_variant_to_option!(KernelEndorsement);
impl_try_from_variant_to_option!(SystemEndorsement);
impl_try_from_variant_to_option!(ContainerEndorsement);
impl_try_from_variant_to_option!(ApplicationEndorsement);
impl_try_from_variant_to_option!(SessionBindingPublicKeyEndorsement);
impl_try_from_variant_to_option!(ConfidentialSpaceEndorsement);

impl From<AmdSevSnpEndorsement> for Variant {
    fn from(value: AmdSevSnpEndorsement) -> Self {
        Variant { id: AMD_SEV_SNP_PLATFORM_ENDORSEMENT_ID.to_vec(), value: value.encode_to_vec() }
    }
}

impl From<FirmwareEndorsement> for Variant {
    fn from(value: FirmwareEndorsement) -> Self {
        Variant { id: FIRMWARE_ENDORSEMENT_ID.to_vec(), value: value.encode_to_vec() }
    }
}

impl From<KernelEndorsement> for Variant {
    fn from(value: KernelEndorsement) -> Self {
        Variant { id: KERNEL_ENDORSEMENT_ID.to_vec(), value: value.encode_to_vec() }
    }
}

impl From<SystemEndorsement> for Variant {
    fn from(value: SystemEndorsement) -> Self {
        Variant { id: SYSTEM_ENDORSEMENT_ID.to_vec(), value: value.encode_to_vec() }
    }
}

impl From<ContainerEndorsement> for Variant {
    fn from(value: ContainerEndorsement) -> Self {
        Variant { id: CONTAINER_ENDORSEMENT_ID.to_vec(), value: value.encode_to_vec() }
    }
}

impl From<ApplicationEndorsement> for Variant {
    fn from(value: ApplicationEndorsement) -> Self {
        Variant { id: APPLICATION_ENDORSEMENT_ID.to_vec(), value: value.encode_to_vec() }
    }
}

impl From<SessionBindingPublicKeyEndorsement> for Variant {
    fn from(value: SessionBindingPublicKeyEndorsement) -> Self {
        Variant {
            id: SESSION_BINDING_PUBLIC_KEY_ENDORSEMENT_ID.to_vec(),
            value: value.encode_to_vec(),
        }
    }
}

impl From<ConfidentialSpaceEndorsement> for Variant {
    fn from(value: ConfidentialSpaceEndorsement) -> Self {
        Variant { id: CONFIDENTIAL_SPACE_ENDORSEMENT_ID.to_vec(), value: value.encode_to_vec() }
    }
}
