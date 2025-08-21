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

#![no_std]

//! This crate contains data structures for parsing Intel TDX quotes.
//!
//! Supports the TD Quote version 4 structures.
//!
//! These structures are based on the Intel TDX DCAP Quoting Library API
//! specification revision 0.9.
//!
//! <https://download.01.org/intel-sgx/latest/dcap-latest/linux/docs/Intel_TDX_DCAP_Quoting_Library_API.pdf>

extern crate alloc;

#[cfg(test)]
extern crate std;

use alloc::boxed::Box;

use bitflags::bitflags;
use nom::{
    bytes::complete::take,
    error::ErrorKind,
    number::complete::{le_u16, le_u32, le_u64},
};
use strum_macros::FromRepr;
use thiserror::Error;

const QUOTE_HEADER_SIZE: usize = 48;
const QUOTE_BODY_SIZE: usize = 584;

/// Possible errors
#[derive(Error, Debug)]
pub enum TdxQuoteError {
    #[error("the bytes does not represent a valid signed TDX quote")]
    InvalidStructure(&'static str),
    #[error("the quote signature verification failed")]
    InvalidSignature,
    #[error("the attestation key verification failed")]
    InvalidAttestationKey,
}

impl From<nom::Err<(&[u8], ErrorKind)>> for TdxQuoteError {
    fn from(_: nom::Err<(&[u8], ErrorKind)>) -> Self {
        TdxQuoteError::InvalidStructure("parsing failed")
    }
}

impl From<nom::Err<nom::error::Error<&[u8]>>> for TdxQuoteError {
    fn from(_: nom::Err<nom::error::Error<&[u8]>>) -> Self {
        TdxQuoteError::InvalidStructure("parsing failed")
    }
}

/// Wrapper for the bytes that represent a signed Intel TDX attestation quote.
pub struct TdxQuoteWrapper<'a> {
    quote_bytes: &'a [u8],
}

impl<'a> TdxQuoteWrapper<'a> {
    pub fn new(quote_bytes: &'a [u8]) -> Self {
        Self { quote_bytes }
    }

    /// Gets the bytes the represent the TDX Quote data.
    pub fn get_quote_data_bytes(&self) -> Result<&'a [u8], TdxQuoteError> {
        let length = QUOTE_HEADER_SIZE + QUOTE_BODY_SIZE;
        if length > self.quote_bytes.len() {
            Err(TdxQuoteError::InvalidStructure("quote_bytes is too small"))
        } else {
            Ok(&self.quote_bytes[..length])
        }
    }

    /// Parses the TDX Quote Header from the Quote Data bytes.
    pub fn parse_quote_header(&self) -> Result<TdxQuoteHeader<'a>, TdxQuoteError> {
        let bytes = self.get_quote_data_bytes()?;
        let (_, header) = TdxQuoteHeader::parse(bytes)?;
        Ok(header)
    }

    /// Parses the TDX Quote from the Quote Data bytes.
    pub fn parse_quote(&self) -> Result<ParsedTdxQuote<'a>, TdxQuoteError> {
        let bytes = self.get_quote_data_bytes()?;
        let (bytes, header) = TdxQuoteHeader::parse(bytes)?;
        let (bytes, body) = TdxQuoteBody::parse(bytes)?;
        if !bytes.is_empty() {
            Err(TdxQuoteError::InvalidStructure("quote_bytes contains unused bytes"))
        } else {
            Ok(ParsedTdxQuote { header, body })
        }
    }

    /// Gets the bytes that represent the TDX Quote signature data.
    pub fn get_signature_data_bytes(&self) -> Result<&'a [u8], TdxQuoteError> {
        let length = QUOTE_HEADER_SIZE + QUOTE_BODY_SIZE;
        if length + size_of::<u32>() > self.quote_bytes.len() {
            return Err(TdxQuoteError::InvalidStructure("quote_bytes is too small"));
        }
        let result = &self.quote_bytes[length..];
        let (result, length) = le_u32::<&[u8], (&[u8], ErrorKind)>(result)?;
        let length = length as usize;
        if length > result.len() {
            Err(TdxQuoteError::InvalidStructure("signature data length is too large"))
        } else {
            Ok(&result[..length])
        }
    }

    /// Parses the quote signature data.
    pub fn parse_signature_data(&self) -> Result<QuoteSignatureData<'a>, TdxQuoteError> {
        let bytes = self.get_signature_data_bytes()?;
        let (_, signature_data) = QuoteSignatureData::parse(bytes)?;
        Ok(signature_data)
    }
}

bitflags! {
    /// The attributes of the Trust Domain.
    #[derive(Debug, Default)]
    pub struct TdAttributes: u64 {
        /// The TD is in debug mode.
        const DEBUG = 1 << 0;
        /// Secure EPT (#VE) is disabled.
        const SEPT_VE_DISABLE = 1 << 28;
        /// The TD is permitted to use the Supervisor Protection Keys.
        const PKS = 1 << 30;
        /// The TD is permitted to use the Key Locker feature.
        const KEY_LOCKER = 1 << 31;
        /// The TD is allowed to use performance monitoring features.
        const PERFMON = 1 << 63;
    }
}

/// The header of a TDX quote.
#[derive(Debug)]
pub struct TdxQuoteHeader<'a> {
    /// The version of the quote format. Must be 4.
    pub version: u16,
    /// The type of the attestation key used.
    ///
    /// Must be 2 (ECDSA-256-with-P-256 curve) for this current version.
    pub att_key_type: u16,
    /// The type of the Trusted Execution Environment.
    ///
    /// Must be 0x00000081 for TDX.
    pub tee_type: u32,
    /// Reserved.
    pub reserved: u32,
    /// The vendor ID of the Quoting Enclave.
    ///
    /// This must be 939A7233F79C4CA9940A0DB3957F0607 (Intel® SGX QE Vendor).
    pub qe_vendor_id: &'a [u8; 16],
    /// Custom user data.
    ///
    /// For the TDX DCAP Quote Generation Libraries the first 16 bytes contain a
    /// Platform Identifier.
    pub user_data: &'a [u8; 20],
}

impl<'a> TdxQuoteHeader<'a> {
    /// Parses a TDX quote header from a byte slice.
    fn parse(bytes: &'a [u8]) -> nom::IResult<&'a [u8], Self> {
        let (rest, version) = le_u16(bytes)?;
        let (rest, att_key_type) = le_u16(rest)?;
        let (rest, tee_type) = le_u32(rest)?;
        let (rest, reserved) = le_u32(rest)?;
        let (rest, qe_vendor_id) = take(16usize)(rest)?;
        let (rest, user_data) = take(20usize)(rest)?;

        Ok((
            rest,
            // Unwrapping is OK here since we know the slices must have the right length if we
            // managed to get this far.
            Self {
                version,
                att_key_type,
                tee_type,
                reserved,
                qe_vendor_id: qe_vendor_id.try_into().unwrap(),
                user_data: user_data.try_into().unwrap(),
            },
        ))
    }
}

/// The body of a TDX quote.
#[derive(Debug)]
pub struct TdxQuoteBody<'a> {
    /// The security version number of the Trusted Execution Environment.
    pub tee_tcb_svn: &'a [u8; 16],
    /// The measurement of the Intel TDX module.
    pub mr_seam: &'a [u8; 48],
    /// The measurement of the TDX module signer.
    pub mrsigner_seam: &'a [u8; 48],
    /// The attributes of the TDX module.
    pub seam_attributes: u64,
    /// The attributes of the Trust Domain (TD).
    pub td_attributes: TdAttributes,
    /// The mask of CPU extended features for the TD.
    pub xfam: u64,
    /// The measurement of the initial contents of the TD.
    pub mr_td: &'a [u8; 48],
    /// The software-defined ID for the TD's configuration.
    pub mr_config_id: &'a [u8; 48],
    /// The software-defined ID for the TD's owner.
    pub mr_owner: &'a [u8; 48],
    /// The software-defined ID for owner-defined configuration.
    pub mr_owner_config: &'a [u8; 48],
    /// Runtime-extendable measurement register 0.
    pub rtmr_0: &'a [u8; 48],
    /// Runtime-extendable measurement register 1.
    pub rtmr_1: &'a [u8; 48],
    /// Runtime-extendable measurement register 2.
    pub rtmr_2: &'a [u8; 48],
    /// Runtime-extendable measurement register 3.
    pub rtmr_3: &'a [u8; 48],
    /// Custom data provided by the TD.
    pub report_data: &'a [u8; 64],
}

impl<'a> TdxQuoteBody<'a> {
    /// Parses a TDX quote body from a byte slice.
    fn parse(bytes: &'a [u8]) -> nom::IResult<&'a [u8], Self> {
        let (rest, tee_tcb_svn) = take(16usize)(bytes)?;
        let (rest, mr_seam) = take(48usize)(rest)?;
        let (rest, mrsigner_seam) = take(48usize)(rest)?;
        let (rest, seam_attributes) = le_u64(rest)?;
        let (rest, td_attributes) = le_u64(rest)?;
        let (rest, xfam) = le_u64(rest)?;
        let (rest, mr_td) = take(48usize)(rest)?;
        let (rest, mr_config_id) = take(48usize)(rest)?;
        let (rest, mr_owner) = take(48usize)(rest)?;
        let (rest, mr_owner_config) = take(48usize)(rest)?;
        let (rest, rtmr_0) = take(48usize)(rest)?;
        let (rest, rtmr_1) = take(48usize)(rest)?;
        let (rest, rtmr_2) = take(48usize)(rest)?;
        let (rest, rtmr_3) = take(48usize)(rest)?;
        let (rest, report_data) = take(64usize)(rest)?;

        Ok((
            rest,
            // Unwrapping is OK here since we know the slices must have the right length if we
            // managed to get this far.
            Self {
                tee_tcb_svn: tee_tcb_svn.try_into().unwrap(),
                mr_seam: mr_seam.try_into().unwrap(),
                mrsigner_seam: mrsigner_seam.try_into().unwrap(),
                seam_attributes,
                td_attributes: TdAttributes::from_bits_truncate(td_attributes),
                xfam,
                mr_td: mr_td.try_into().unwrap(),
                mr_config_id: mr_config_id.try_into().unwrap(),
                mr_owner: mr_owner.try_into().unwrap(),
                mr_owner_config: mr_owner_config.try_into().unwrap(),
                rtmr_0: rtmr_0.try_into().unwrap(),
                rtmr_1: rtmr_1.try_into().unwrap(),
                rtmr_2: rtmr_2.try_into().unwrap(),
                rtmr_3: rtmr_3.try_into().unwrap(),
                report_data: report_data.try_into().unwrap(),
            },
        ))
    }
}

/// A parsed TDX quote.
#[derive(Debug)]
pub struct ParsedTdxQuote<'a> {
    /// The header of the quote.
    pub header: TdxQuoteHeader<'a>,
    /// The body of the quote.
    pub body: TdxQuoteBody<'a>,
}

/// The type of the Quoting Enclave (QE) certification data.
///
/// Note: This enum must remain exactly in sync with QeCertificationData.
#[derive(Debug, FromRepr)]
#[repr(u16)]
pub enum QeCertificationDataType {
    /// Provisioning Certification Key (PCK) identifier: Platform Provisioning
    /// (PP) ID in plain text, CPU SVN, and Provisioning Certification
    /// Enclave (PCE) SVN.
    PckIdentifierPpIdCpuSvnPceSvn = 1,
    /// PCK identifier: PP ID encrypted using RSA-2048-OAEP, CPU SVN, and PCE
    /// SVN.
    PckIdentifierPpIdRSA2048CpuSvnPceSvn = 2,
    /// PCK identifier: PP ID encrypted using RSA-3072-OAEP, CPU SVN, and PCE
    /// SVN.
    PckIdentifierPpIdRSA3072CpuSvnPceSvn = 3,
    /// PCK Leaf Certificate in plain text (currently not supported).
    PckLeafCert = 4,
    /// Concatenated PCK Cert Chain.
    PckCertChain = 5,
    /// QE Report Certification Data.
    QeReportCertificationData = 6,
    /// Platform manifest (currently not supported).
    PlatformManifest = 7,
}

/// The QE Certification Data.
///
/// This enum contains the data required to verify the QE Report Signature.
#[derive(Debug)]
#[repr(u16)]
pub enum QeCertificationData<'a> {
    /// Provisioning Certification Key (PCK) identifier: Platform Provisioning
    /// (PP) ID in plain text, CPU SVN, and Provisioning Certification
    /// Enclave (PCE) SVN.
    PckIdentifierPpIdCpuSvnPceSvn(&'a [u8]) = 1,
    /// PCK identifier: PP ID encrypted using RSA-2048-OAEP, CPU SVN, and PCE
    /// SVN.
    PckIdentifierPpIdRSA2048CpuSvnPceSvn(&'a [u8]) = 2,
    /// PCK identifier: PP ID encrypted using RSA-3072-OAEP, CPU SVN, and PCE
    /// SVN.
    PckIdentifierPpIdRSA3072CpuSvnPceSvn(&'a [u8]) = 3,
    /// PCK Leaf Certificate in plain text (currently not supported).
    PckLeafCert(&'a [u8]) = 4,
    /// Concatenated PCK Cert Chain.
    PckCertChain(&'a [u8]) = 5,
    /// QE Report Certification Data.
    QeReportCertificationData(Box<QeReportCertificationData<'a>>) = 6,
    /// Platform manifest (currently not supported).
    PlatformManifest(&'a [u8]) = 7,
}

impl<'a> QeCertificationData<'a> {
    /// Parses a TDX quote header from a byte slice.
    fn parse(bytes: &'a [u8]) -> nom::IResult<&'a [u8], Self> {
        let (rest, certification_data_type) = le_u16(bytes)?;
        let (rest, length) = le_u32(rest)?;
        let (rest, bytes) = take(length)(rest)?;
        let certification_data_type =
            QeCertificationDataType::from_repr(certification_data_type)
                .ok_or(nom::Err::Failure(nom::error::Error::new(bytes, ErrorKind::Fail)))?;
        match certification_data_type {
            QeCertificationDataType::PckIdentifierPpIdCpuSvnPceSvn => {
                Ok((rest, QeCertificationData::PckIdentifierPpIdCpuSvnPceSvn(bytes)))
            }
            QeCertificationDataType::PckIdentifierPpIdRSA2048CpuSvnPceSvn => {
                Ok((rest, QeCertificationData::PckIdentifierPpIdRSA2048CpuSvnPceSvn(bytes)))
            }
            QeCertificationDataType::PckIdentifierPpIdRSA3072CpuSvnPceSvn => {
                Ok((rest, QeCertificationData::PckIdentifierPpIdRSA3072CpuSvnPceSvn(bytes)))
            }
            QeCertificationDataType::PckLeafCert => {
                Ok((rest, QeCertificationData::PckLeafCert(bytes)))
            }
            QeCertificationDataType::PckCertChain => {
                Ok((rest, QeCertificationData::PckCertChain(bytes)))
            }
            QeCertificationDataType::QeReportCertificationData => {
                let (_, report_certification_data) = QeReportCertificationData::parse(bytes)?;
                Ok((
                    rest,
                    QeCertificationData::QeReportCertificationData(Box::new(
                        report_certification_data,
                    )),
                ))
            }
            QeCertificationDataType::PlatformManifest => {
                Ok((rest, QeCertificationData::PlatformManifest(bytes)))
            }
        }
    }
}

/// The body of an enclave report.
#[derive(Debug)]
pub struct EnclaveReportBody<'a> {
    /// The security version of the hardware components.
    pub cpu_svn: &'a [u8; 16],
    /// Which SECS.MISCSELECT settings are used in the enclave.
    pub misc_select: u32,
    /// Reserved.
    pub reserved1: &'a [u8; 28],
    /// Any special capabilities the enclave possesses.
    pub attributes: &'a [u8; 16],
    /// The hash of the enclave measurement.
    pub mr_enclave: &'a [u8; 32],
    /// Reserved.
    pub reserved2: &'a [u8; 32],
    /// The hash of the key used to sign the enclave.
    pub mr_signer: &'a [u8; 32],
    /// Reserved.
    pub reserved3: &'a [u8; 96],
    /// The product ID of the enclave.
    pub isv_prod_id: u16,
    /// The security version of the enclave.
    pub isv_svn: u16,
    /// Reserved.
    pub reserved4: &'a [u8; 60],
    /// Data provided by the user.
    pub report_data: &'a [u8; 64],
}

impl<'a> EnclaveReportBody<'a> {
    /// Parses an enclave report body from a byte slice.
    fn parse(bytes: &'a [u8]) -> nom::IResult<&'a [u8], Self> {
        let (rest, cpu_svn) = take(16usize)(bytes)?;
        let (rest, misc_select) = le_u32(rest)?;
        let (rest, reserved1) = take(28usize)(rest)?;
        let (rest, attributes) = take(16usize)(rest)?;
        let (rest, mr_enclave) = take(32usize)(rest)?;
        let (rest, reserved2) = take(32usize)(rest)?;
        let (rest, mr_signer) = take(32usize)(rest)?;
        let (rest, reserved3) = take(96usize)(rest)?;
        let (rest, isv_prod_id) = le_u16(rest)?;
        let (rest, isv_svn) = le_u16(rest)?;
        let (rest, reserved4) = take(60usize)(rest)?;
        let (rest, report_data) = take(64usize)(rest)?;

        Ok((
            rest,
            // Unwrapping is OK here since we know the slices must have the right length if we
            // managed to get this far.
            Self {
                cpu_svn: cpu_svn.try_into().unwrap(),
                misc_select,
                reserved1: reserved1.try_into().unwrap(),
                attributes: attributes.try_into().unwrap(),
                mr_enclave: mr_enclave.try_into().unwrap(),
                reserved2: reserved2.try_into().unwrap(),
                mr_signer: mr_signer.try_into().unwrap(),
                reserved3: reserved3.try_into().unwrap(),
                isv_prod_id,
                isv_svn,
                reserved4: reserved4.try_into().unwrap(),
                report_data: report_data.try_into().unwrap(),
            },
        ))
    }
}

/// The signature over a quote and associated data.
#[derive(Debug)]
pub struct QuoteSignatureData<'a> {
    /// The ECDSA P-256 signature of the quote using the attestation key
    /// generated by the quoting enclave.
    pub quote_signature: &'a [u8; 64],
    /// The public key of the attestation key generated by the quoting enclave.
    pub ecdsa_attestation_key: &'a [u8; 64],
    /// The data required to validate the attestation key.
    pub certification_data: QeCertificationData<'a>,
}

impl<'a> QuoteSignatureData<'a> {
    fn parse(bytes: &'a [u8]) -> nom::IResult<&'a [u8], Self> {
        let (rest, quote_signature) = take(64usize)(bytes)?;
        let (rest, ecdsa_attestation_key) = take(64usize)(rest)?;
        let (rest, certification_data) = QeCertificationData::parse(rest)?;
        Ok((
            rest,
            // Unwrapping is OK here since we know the slices must have the right length if
            // we managed to get this far.
            QuoteSignatureData {
                quote_signature: quote_signature.try_into().unwrap(),
                ecdsa_attestation_key: ecdsa_attestation_key.try_into().unwrap(),
                certification_data,
            },
        ))
    }
}

/// Certification data for a Quoting Enclave report.
#[derive(Debug)]
pub struct QeReportCertificationData<'a> {
    /// The bytes representing the report for the quoting enclave.
    pub report_body: &'a [u8; 384],
    /// The signature over the report body.
    pub signature: &'a [u8; 64],
    /// Additional optional data covered by the signature.
    pub authentication_data: &'a [u8],
    /// The data required to validate the signature.
    pub certification_data: QeCertificationData<'a>,
}

impl<'a> QeReportCertificationData<'a> {
    fn parse(bytes: &'a [u8]) -> nom::IResult<&'a [u8], Self> {
        let (rest, report_body) = take(384usize)(bytes)?;
        let (rest, signature) = take(64usize)(rest)?;
        let (rest, authentication_data_length) = le_u16(rest)?;
        let (rest, authentication_data) = take(authentication_data_length as usize)(rest)?;
        let (rest, certification_data) = QeCertificationData::parse(rest)?;
        Ok((
            rest,
            // Unwrapping is OK here since we know the slices must have the right length if
            // we managed to get this far.
            QeReportCertificationData {
                report_body: report_body.try_into().unwrap(),
                signature: signature.try_into().unwrap(),
                authentication_data,
                certification_data,
            },
        ))
    }

    /// Parses the enclave report body.
    pub fn parse_enclave_report_body(&self) -> Result<EnclaveReportBody, TdxQuoteError> {
        let (_, result) = EnclaveReportBody::parse(self.report_body)?;
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use googletest::prelude::*;
    use oak_proto_rust::oak::attestation::v1::TeePlatform;
    use test_util::AttestationData;

    use super::*;

    fn get_evidence_quote_bytes() -> Vec<u8> {
        let d = AttestationData::load_tdx_oc();
        d.evidence.root_layer.expect("no root layer").remote_attestation_report
    }

    #[test]
    fn ensure_evidence_is_for_tdx() {
        let d = AttestationData::load_tdx_oc();
        assert_that!(
            d.evidence.root_layer.as_ref().expect("no root layer").platform,
            eq(TeePlatform::IntelTdx as i32)
        );
    }

    #[test]
    fn parse_tdx_quote_header() {
        let quote_buffer = get_evidence_quote_bytes();
        let (_, header) =
            TdxQuoteHeader::parse(quote_buffer.as_slice()).expect("header parsing failed");
        // Currently version 4 is supported.
        assert_that!(header.version, eq(4));
        assert_that!(header.reserved, eq(0));
        // ECDSA-256-with-P-256 curve.
        assert_that!(header.att_key_type, eq(2));
        // Intel TDX.
        assert_that!(header.tee_type, eq(0x00000081));
        assert_that!(
            header.qe_vendor_id,
            // Intel SGX Quoting Enclave Vendor.
            eq(&[
                0x93, 0x9A, 0x72, 0x33, 0xF7, 0x9C, 0x4C, 0xA9, 0x94, 0x0A, 0x0D, 0xB3, 0x95, 0x7F,
                0x06, 0x07
            ])
        );
        assert_that!(header.user_data, eq(&[0u8; 20]));
    }

    #[test]
    fn parse_tdx_quote_body() {
        let quote_buffer = get_evidence_quote_bytes();
        let (rest, _) =
            TdxQuoteHeader::parse(quote_buffer.as_slice()).expect("header parsing failed");
        let (_, body) = TdxQuoteBody::parse(rest).expect("body parsing failed");
        assert_that!(body.seam_attributes, eq(0));
        assert_that!(body.mr_config_id, eq(&[0u8; 48]));
        assert_that!(body.mr_owner, eq(&[0u8; 48]));
        assert_that!(body.mr_owner_config, eq(&[0u8; 48]));
        assert_that!(body.rtmr_0, eq(&[0u8; 48]));
        assert_that!(body.rtmr_1, eq(&[0u8; 48]));
        assert_that!(body.rtmr_2, not(eq(&[0u8; 48])));
        assert_that!(body.rtmr_3, eq(&[0u8; 48]));
        assert_that!(body.report_data, eq(&[0u8; 64]));
    }

    #[test]
    fn parse_tdx_quote_from_wrapper() {
        let quote_buffer = get_evidence_quote_bytes();
        let wrapper = TdxQuoteWrapper { quote_bytes: quote_buffer.as_slice() };

        let quote = wrapper.parse_quote().expect("quote parsing failed");

        // Currently version 4 is supported.
        assert_that!(quote.header.version, eq(4));
        assert_that!(quote.header.reserved, eq(0));
        // Intel TDX.
        assert_that!(quote.header.tee_type, eq(0x00000081));
        assert_that!(
            quote.header.qe_vendor_id,
            // Intel SGX Quoting Enclave Vendor.
            eq(&[
                0x93, 0x9A, 0x72, 0x33, 0xF7, 0x9C, 0x4C, 0xA9, 0x94, 0x0A, 0x0D, 0xB3, 0x95, 0x7F,
                0x06, 0x07
            ])
        );
        assert_that!(quote.header.user_data, eq(&[0u8; 20]));
        assert_that!(quote.body.seam_attributes, eq(0));
        assert_that!(quote.body.mr_config_id, eq(&[0u8; 48]));
        assert_that!(quote.body.mr_owner, eq(&[0u8; 48]));
        assert_that!(quote.body.mr_owner_config, eq(&[0u8; 48]));
        assert_that!(quote.body.rtmr_0, eq(&[0u8; 48]));
        assert_that!(quote.body.rtmr_1, eq(&[0u8; 48]));
        assert_that!(quote.body.rtmr_2, not(eq(&[0u8; 48])));
        assert_that!(quote.body.rtmr_3, eq(&[0u8; 48]));
        assert_that!(quote.body.report_data, eq(&[0u8; 64]));
    }

    #[test]
    fn check_signature_data_length() {
        let quote_buffer = get_evidence_quote_bytes();
        let wrapper = TdxQuoteWrapper { quote_bytes: quote_buffer.as_slice() };
        let signature_data =
            wrapper.get_signature_data_bytes().expect("couldn't get signature data bytes");
        let expected = quote_buffer.len() - QUOTE_HEADER_SIZE - QUOTE_BODY_SIZE - size_of::<u32>();
        assert_that!(signature_data.len(), le(expected));
    }

    #[test]
    fn parse_signature_data() {
        let quote_buffer = get_evidence_quote_bytes();
        let wrapper = TdxQuoteWrapper { quote_bytes: quote_buffer.as_slice() };

        let signature_data = wrapper.parse_signature_data().expect("signature data parsing failed");

        let report_certification =
            if let QeCertificationData::QeReportCertificationData(report_certification) =
                signature_data.certification_data
            {
                report_certification
            } else {
                panic!("signature data contains the wrong type of certification data");
            };

        std::assert!(std::matches!(
            report_certification.certification_data,
            QeCertificationData::PckCertChain(_)
        ));

        let enclave_report = report_certification
            .parse_enclave_report_body()
            .expect("enclave report parsing failed");
        assert_that!(enclave_report.reserved1, eq(&[0u8; 28]));
        assert_that!(enclave_report.reserved2, eq(&[0u8; 32]));
        assert_that!(enclave_report.reserved3, eq(&[0u8; 96]));
        assert_that!(enclave_report.reserved4, eq(&[0u8; 60]));
        assert_that!(enclave_report.report_data, not(eq(&[0u8; 64])));
    }
}
