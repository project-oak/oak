//
// Copyright 2024 The Project Oak Authors
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

use alloc::{string::String, vec};

use anyhow::Context;
use oak_attestation_verification_types::policy::Policy;
use oak_proto_rust::oak::{
    Variant,
    attestation::v1::{
        BinaryReferenceValue, Digests, EventAttestationResults, KernelBinaryReferenceValue,
        KernelDigests, KernelEndorsement, KernelLayerReferenceValues, Stage0Measurements,
        TextReferenceValue, binary_reference_value, kernel_binary_reference_value,
        text_reference_value,
    },
};
use oak_time::Instant;

use crate::{
    compare::compare_kernel_layer_measurement_digests,
    expect::acquire_kernel_event_expected_values,
    extract::stage0_measurements_to_kernel_layer_data, util::decode_event_proto,
};

pub struct KernelPolicy {
    reference_values: KernelLayerReferenceValues,
}

impl KernelPolicy {
    pub fn new(reference_values: &KernelLayerReferenceValues) -> Self {
        Self { reference_values: reference_values.clone() }
    }

    /// Returns reference values that accept only the version in the evidence.
    ///
    /// The evidence should contain the same information that would be passed to
    /// `verify`.
    pub fn evidence_to_reference_values(
        evidence: &[u8],
    ) -> anyhow::Result<KernelLayerReferenceValues> {
        let event =
            stage0_measurements_to_kernel_layer_data(decode_event_proto::<Stage0Measurements>(
                "type.googleapis.com/oak.attestation.v1.Stage0Measurements",
                evidence,
            )?);
        Ok(KernelLayerReferenceValues {
            kernel: Some(KernelBinaryReferenceValue {
                r#type: Some(kernel_binary_reference_value::Type::Digests(KernelDigests {
                    image: Some(Digests {
                        digests: vec![event.kernel_image.context("no kernel_image in evidence")?],
                    }),
                    setup_data: Some(Digests {
                        digests: vec![
                            event.kernel_setup_data.context("no kernel_setup_data in evidence")?,
                        ],
                    }),
                })),
            }),
            kernel_cmd_line_text: Some(Self::get_cmd_line_reference_value(
                event.kernel_raw_cmd_line.context("no kernel_raw_cmd_line in evidence")?,
            )),
            init_ram_fs: Some(BinaryReferenceValue {
                r#type: Some(binary_reference_value::Type::Digests(Digests {
                    digests: vec![event.init_ram_fs.context("no missing init_ram_fs in evidence")?],
                })),
            }),
            memory_map: Some(BinaryReferenceValue {
                r#type: Some(binary_reference_value::Type::Digests(Digests {
                    digests: vec![event.memory_map.context("no memory_map in evidence")?],
                })),
            }),
            acpi: Some(BinaryReferenceValue {
                r#type: Some(binary_reference_value::Type::Digests(Digests {
                    digests: vec![event.acpi.context("no acpi in evidence")?],
                })),
            }),
        })
    }

    #[cfg(feature = "regex")]
    fn get_cmd_line_reference_value(cmd_line: String) -> TextReferenceValue {
        use alloc::format;

        use oak_proto_rust::oak::attestation::v1::Regex;

        // Sanitize the kernel command line. It must match literally and in
        // full, except:
        //   - Allow the ramdisk size to differ.
        //   - Allow extra flags at the end.
        let kernel_args = cmd_line.split_once(" -- ").map_or(cmd_line.as_str(), |(args, _)| args);
        let kernel_args = regex_lite::Regex::new(r"\bbrd\\\.rd_size=[1-9][0-9]*\b")
            .unwrap()
            .replace(&regex_lite::escape(kernel_args), r"brd\.rd_size=[1-9][0-9]*")
            .into_owned();
        TextReferenceValue {
            r#type: Some(text_reference_value::Type::Regex(Regex {
                value: format!("^{kernel_args}(| -- .*)$"),
            })),
        }
    }

    #[cfg(not(feature = "regex"))]
    fn get_cmd_line_reference_value(cmd_line: String) -> TextReferenceValue {
        use oak_proto_rust::oak::attestation::v1::StringLiterals;

        TextReferenceValue {
            r#type: Some(text_reference_value::Type::StringLiterals(StringLiterals {
                value: vec![cmd_line],
            })),
        }
    }
}

impl Policy<[u8]> for KernelPolicy {
    fn verify(
        &self,
        verification_time: Instant,
        evidence: &[u8],
        endorsement: &Variant,
    ) -> anyhow::Result<EventAttestationResults> {
        let event =
            stage0_measurements_to_kernel_layer_data(decode_event_proto::<Stage0Measurements>(
                "type.googleapis.com/oak.attestation.v1.Stage0Measurements",
                evidence,
            )?);
        let endorsement: Option<KernelEndorsement> =
            endorsement.try_into().map_err(anyhow::Error::msg)?;

        let (expected_values, _tlog_verifications) = acquire_kernel_event_expected_values(
            verification_time.into_unix_millis(),
            endorsement.as_ref(),
            &self.reference_values,
        )
        .context("acquiring kernel event expected values")?;

        compare_kernel_layer_measurement_digests(&event, &expected_values)
            .context("comparing kernel event digests")?;

        // TODO: b/356631062 - Return detailed attestation results.
        Ok(EventAttestationResults { ..Default::default() })
    }
}

#[cfg(test)]
mod tests {
    use test_util::{AttestationData, get_oc_reference_values, get_rk_reference_values};

    use super::*;

    const KERNEL_EVENT_INDEX: usize = 0;

    #[test]
    fn verify_oc_success() {
        let d = AttestationData::load_milan_oc_release();
        let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
        let endorsement = &d.endorsements.events[KERNEL_EVENT_INDEX];
        let ref_values = get_oc_reference_values(&d.reference_values);
        let policy = KernelPolicy::new(ref_values.kernel_layer.as_ref().unwrap());

        let result = policy.verify(d.make_valid_time(), event, endorsement);

        // TODO: b/356631062 - Verify detailed attestation results.
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn verify_rk_success() {
        let d: AttestationData = AttestationData::load_milan_rk_release();
        let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
        let endorsement = &d.endorsements.events[KERNEL_EVENT_INDEX];
        let ref_values = get_rk_reference_values(&d.reference_values);
        let policy = KernelPolicy::new(ref_values.kernel_layer.as_ref().unwrap());

        let result = policy.verify(d.make_valid_time(), event, endorsement);

        // TODO: b/356631062 - Verify detailed attestation results.
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn evidence_to_reference_values_oc_succeeds() {
        let d = AttestationData::load_milan_oc_release();
        let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];

        let rv = KernelPolicy::evidence_to_reference_values(event)
            .expect("evidence_to_reference_values failed");
        assert!(
            matches!(
                rv,
                KernelLayerReferenceValues {
                    kernel: Some(KernelBinaryReferenceValue {
                        r#type: Some(kernel_binary_reference_value::Type::Digests(..))
                    }),
                    kernel_cmd_line_text: Some(..),
                    init_ram_fs: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(..))
                    }),
                    memory_map: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(..))
                    }),
                    acpi: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(..))
                    }),
                }
            ),
            "reference values missing fields: {:?}",
            rv
        );
        #[cfg(feature = "regex")]
        assert!(
            matches!(
                rv.kernel_cmd_line_text.as_ref().unwrap(),
                TextReferenceValue { r#type: Some(text_reference_value::Type::Regex(..)) }
            ),
            "kernel_cmd_line_text reference value missing fields: {:?}",
            rv.kernel_cmd_line_text.as_ref().unwrap()
        );
        #[cfg(not(feature = "regex"))]
        assert!(
            matches!(
                rv.kernel_cmd_line_text.as_ref().unwrap(),
                TextReferenceValue { r#type: Some(text_reference_value::Type::StringLiterals(..)) }
            ),
            "kernel_cmd_line_text reference value missing fields: {:?}",
            rv.kernel_cmd_line_text.as_ref().unwrap()
        );

        let result = KernelPolicy::new(&rv).verify(d.make_valid_time(), event, &Variant::default());
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    #[test]
    fn evidence_to_reference_values_rk_succeeds() {
        let d = AttestationData::load_milan_rk_release();
        let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];

        let rv = KernelPolicy::evidence_to_reference_values(event)
            .expect("evidence_to_reference_values failed");
        assert!(
            matches!(
                rv,
                KernelLayerReferenceValues {
                    kernel: Some(KernelBinaryReferenceValue {
                        r#type: Some(kernel_binary_reference_value::Type::Digests(..))
                    }),
                    kernel_cmd_line_text: Some(..),
                    init_ram_fs: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(..))
                    }),
                    memory_map: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(..))
                    }),
                    acpi: Some(BinaryReferenceValue {
                        r#type: Some(binary_reference_value::Type::Digests(..))
                    }),
                }
            ),
            "reference values missing fields: {:?}",
            rv
        );
        #[cfg(feature = "regex")]
        assert!(
            matches!(
                rv.kernel_cmd_line_text.as_ref().unwrap(),
                TextReferenceValue { r#type: Some(text_reference_value::Type::Regex(..)) }
            ),
            "kernel_cmd_line_text reference value missing fields: {:?}",
            rv.kernel_cmd_line_text.as_ref().unwrap()
        );
        #[cfg(not(feature = "regex"))]
        assert!(
            matches!(
                rv.kernel_cmd_line_text.as_ref().unwrap(),
                TextReferenceValue { r#type: Some(text_reference_value::Type::StringLiterals(..)) }
            ),
            "kernel_cmd_line_text reference value missing fields: {:?}",
            rv.kernel_cmd_line_text.as_ref().unwrap()
        );

        let result = KernelPolicy::new(&rv).verify(d.make_valid_time(), event, &Variant::default());
        assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
    }

    /// Returns `encoded_event` with its kernel command line replaced by
    /// `modify(<current command line>)`.
    fn with_cmd_line(encoded_event: &[u8], modify: impl FnOnce(&str) -> String) -> Vec<u8> {
        use oak_proto_rust::oak::attestation::v1::Event;
        use prost::Message;

        let mut event = Event::decode(encoded_event).expect("couldn't decode event");
        let any = event.event.as_mut().expect("no event payload");
        let mut measurements =
            Stage0Measurements::decode(any.value.as_slice()).expect("couldn't decode measurements");
        measurements.kernel_cmdline = modify(&measurements.kernel_cmdline);
        any.value = measurements.encode_to_vec();
        event.encode_to_vec()
    }

    #[test]
    fn evidence_to_reference_values_rejects_other_cmd_line() {
        let d = AttestationData::load_milan_oc_release();
        let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
        let rv = KernelPolicy::evidence_to_reference_values(event)
            .expect("evidence_to_reference_values failed");
        let policy = KernelPolicy::new(&rv);

        let prepended = with_cmd_line(event, |cmd_line| format!("mitigations=off {cmd_line}"));
        let renamed = with_cmd_line(event, |cmd_line| cmd_line.replacen("brd.", "brdX", 1));
        for modified in [prepended, renamed] {
            let result = policy.verify(d.make_valid_time(), &modified, &Variant::default());
            assert!(result.is_err(), "modified kernel command line was accepted");
        }
    }

    #[test]
    #[cfg(feature = "regex")]
    fn evidence_to_reference_values_allows_ram_disk_size_and_trailing_args() {
        let d = AttestationData::load_milan_oc_release();
        let event = &d.evidence.event_log.as_ref().unwrap().encoded_events[KERNEL_EVENT_INDEX];
        let rv = KernelPolicy::evidence_to_reference_values(event)
            .expect("evidence_to_reference_values failed");
        let policy = KernelPolicy::new(&rv);

        let resized = with_cmd_line(event, |cmd_line| {
            cmd_line.replacen("brd.rd_size=3072000", "brd.rd_size=1024", 1)
        });
        let with_args = with_cmd_line(event, |cmd_line| format!("{cmd_line} -- --some-arg"));
        for modified in [resized, with_args] {
            let result = policy.verify(d.make_valid_time(), &modified, &Variant::default());
            assert!(result.is_ok(), "Failed: {:?}", result.err().unwrap());
        }
    }
}
