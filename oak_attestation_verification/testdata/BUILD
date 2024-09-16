#
# Copyright 2022 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

# A valid Transparent Release endorsement bundle with `normal` usage.
filegroup(
    name = "endorsement",
    srcs = [
        "endorsement.json",
        "endorsement.json.sig",
        "logentry.json",
        "endorser_public_key.pem",
        # Public key of the Rekor instance hosted by sigstore.dev. It is downloaded
        # from https://rekor.sigstore.dev/api/v1/log/publicKey.
        "rekor_public_key.pem",
    ],
)

filegroup(
    name = "cb_evidence",
    srcs = [
        "cb_endorsement.binarypb",
        "cb_evidence.binarypb",
        "cb_reference_values.binarypb",
    ],
    visibility = ["//visibility:private"],
)

filegroup(
    name = "fake_evidence",
    srcs = [
        "fake_evidence.binarypb",
        "fake_expected_values.binarypb",
    ],
)

filegroup(
    name = "evidence",
    srcs = [
        ":cb_evidence",
        ":fake_evidence",
        "genoa_oc_evidence.binarypb",
        "genoa_oc_reference_values.binarypb",
        "oc_evidence.binarypb",
        # The VCEK cert needs to match the hardware ID of the attestation report in the
        # test evidence proto. The additional parameters in the URL encode the reported
        # TCB version in the attestation report.
        #
        # URL for downloading the VCEK cert:
        # https://kdsintf.amd.com/vcek/v1/Milan/cd3c4e6b5b64026ac135d76f888ea6bcc1351ec610d64b0af4028422b84c17ad2571905acfe2eb2181c119df4241e94a926d1b06c02e82845416202151212fdd?ucodeSPL=168&snpSPL=8&teeSPL=0&blSPL=3
        # ARPT reported TCB version: ucodeSPL=168&snpSPL=8&teeSPL=0&blSPL=3
        # ARPT current  TCB version: ucodeSPL=209&snpSPL=14&teeSPL=0&blSPL=3
        "oc_vcek_milan.der",
        "oc_vcek_milan.pem",
        "rk_evidence.binarypb",
        "rk_evidence_20240312.binarypb",
        "rk_vcek_milan.der",
        "vcek_genoa.der",
    ],
)
