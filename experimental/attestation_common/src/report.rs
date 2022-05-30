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

use anyhow::Context;
use openssl::{nid::Nid, x509::X509Extension};
use x509_parser::der_parser::{self, oid::Oid};

// Using `NETSCAPE_COMMENT` extension since `rust-openssl` doesn't support custom extensions yet.
//
// <https://github.com/sfackler/rust-openssl/issues/1411>
//
// <https://www.alvestrand.no/objectid/2.16.840.1.113730.1.13.html>
pub const TEE_EXTENSION_OID: Oid<'static> = der_parser::oid!(2.16.840 .1 .113730 .1 .13);

/// Serializes [`AttestationInfo`] into a custom [`X509Extension`].
pub fn to_x509_extension(attestation_report_string: &str) -> anyhow::Result<X509Extension> {
    // [`Nid::NETSCAPE_COMMENT`] is a numerical identifier for an OpenSSL object that
    // corresponds to an X.509 extension implementation.
    X509Extension::new_nid(None, None, Nid::NETSCAPE_COMMENT, attestation_report_string)
        .context("Couldn't create X.509 extension")
}
