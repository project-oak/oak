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

use alloc::{boxed::Box, vec::Vec};

use bitflags::bitflags;
use nom::{
    bytes::complete::take,
    number::complete::{le_u16, le_u32, le_u64},
};

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
pub struct TdxQuoteHeader {
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
    pub qe_vendor_id: [u8; 16],
    /// Custom user data.
    ///
    /// For the TDX DCAP Quote Generation Libraries the first 16 bytes contain a
    /// Platform Identifier.
    pub user_data: [u8; 20],
}

impl TdxQuoteHeader {
    /// Parses a TDX quote header from a byte slice.
    #[allow(unused)]
    fn parse(bytes: &[u8]) -> nom::IResult<&[u8], Self> {
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
pub struct TdxQuoteBody {
    /// The security version number of the Trusted Execution Environment.
    pub tee_tcb_svn: [u8; 16],
    /// The measurement of the Intel TDX module.
    pub mr_seam: [u8; 48],
    /// The measurement of the TDX module signer.
    pub mrsigner_seam: [u8; 48],
    /// The attributes of the TDX module.
    pub seam_attributes: u64,
    /// The attributes of the Trust Domain (TD).
    pub td_attributes: TdAttributes,
    /// The mask of CPU extended features for the TD.
    pub xfam: u64,
    /// The measurement of the initial contents of the TD.
    pub mr_td: [u8; 48],
    /// The software-defined ID for the TD's configuration.
    pub mr_config_id: [u8; 48],
    /// The software-defined ID for the TD's owner.
    pub mr_owner: [u8; 48],
    /// The software-defined ID for owner-defined configuration.
    pub mr_owner_config: [u8; 48],
    /// Runtime-extendable measurement register 0.
    pub rtmr_0: [u8; 48],
    /// Runtime-extendable measurement register 1.
    pub rtmr_1: [u8; 48],
    /// Runtime-extendable measurement register 2.
    pub rtmr_2: [u8; 48],
    /// Runtime-extendable measurement register 3.
    pub rtmr_3: [u8; 48],
    /// Custom data provided by the TD.
    pub report_data: [u8; 64],
}

impl TdxQuoteBody {
    /// Parses a TDX quote body from a byte slice.
    #[allow(unused)]
    fn parse(bytes: &[u8]) -> nom::IResult<&[u8], Self> {
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
pub struct ParsedTdxQuote {
    /// The header of the quote.
    pub header: TdxQuoteHeader,
    /// The body of the quote.
    pub body: TdxQuoteBody,
}

/// The QE Certification Data.
///
/// This enum contains the data required to verify the QE Report Signature.
#[derive(Debug)]
#[repr(u16)]
pub enum QeCertificationData {
    /// Provisioning Certification Key (PCK) identifier: Platform Provisioning
    /// (PP) ID in plain text, CPU SVN, and Provisioning Certification
    /// Enclave (PCE) SVN.
    PckIdentifierPpIdCpuSvnPceSvn(Vec<u8>) = 1,
    /// PCK identifier: PP ID encrypted using RSA-2048-OAEP, CPU SVN, and PCE
    /// SVN.
    PckIdentifierPpIdRSA2048CpuSvnPceSvn(Vec<u8>) = 2,
    /// PCK identifier: PP ID encrypted using RSA-3072-OAEP, CPU SVN, and PCE
    /// SVN.
    PckIdentifierPpIdRSA3072CpuSvnPceSvn(Vec<u8>) = 3,
    /// PCK Leaf Certificate in plain text (currently not supported).
    PckLeafCert(Vec<u8>) = 4,
    /// Concatenated PCK Cert Chain.
    PckCertChain(Vec<u8>) = 5,
    /// QE Report Certification Data.
    QeReportCertificationData(Box<QeReportCertificationData>) = 6,
    /// Platform manifest (currently not supported).
    PlatformManifest(Vec<u8>) = 7,
}

/// The body of an enclave report.
#[derive(Debug)]
pub struct EnclaveReportBody {
    /// The security version of the hardware components.
    pub cpu_svn: [u8; 16],
    /// Which SECS.MISCSELECT settings are used in the enclave.
    pub misc_select: u32,
    /// Reserved.
    pub reserved1: [u8; 28],
    /// Any special capabilities the enclave possesses.
    pub attributes: [u8; 16],
    /// The hash of the enclave measurement.
    pub mr_enclave: [u8; 32],
    /// Reserved.
    pub reserved2: [u8; 32],
    /// The hash of the key used to sign the enclave.
    pub mr_signer: [u8; 32],
    /// Reserved.
    pub reserved3: [u8; 96],
    /// The product ID of the enclave.
    pub isv_prod_id: u16,
    /// The security version of the enclave.
    pub isv_svn: u16,
    /// Reserved.
    pub reserved4: [u8; 60],
    /// Data provided by the user.
    pub report_data: [u8; 64],
}

impl EnclaveReportBody {
    /// Parses an enclave report body from a byte slice.
    #[allow(unused)]
    fn parse(bytes: &[u8]) -> nom::IResult<&[u8], Self> {
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
pub struct QuoteSignatureData {
    /// The ECDSA P-256 signature of the quote using the attestation key
    /// generated by the quoting enclave.
    pub quote_signature: [u8; 64],
    /// The public key of the attestation key generated by the quoting enclave.
    pub ecdsa_attestation_key: [u8; 64],
    /// The data required to validate the attestation key.
    pub certification_data: QeCertificationData,
}

/// Certification data for a Quoting Enclave report.
#[derive(Debug)]
pub struct QeReportCertificationData {
    /// The bytes representing the report for the quoting enclave.
    pub report_body: [u8; 384],
    /// The signature over the report body.
    pub signature: [u8; 64],
    /// Additional optional data covered by the signature.
    pub authentication_data: Vec<u8>,
    /// The data required to validate the signature.
    pub certification_data: QeCertificationData,
}
