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
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

exports_files([
    "cb_evidence.binarypb",
    "cb_endorsement.binarypb",
    "cb_reference_values.binarypb",
    "endorsement.json",
    "endorsement.json.sig",
    "fake_evidence.binarypb",
    "fake_expected_values.binarypb",
    "genoa_oc_evidence.binarypb",
    "genoa_oc_reference_values.binarypb",
    "logentry.json",
    "oak_containers_stage1.pem",
    "oak-development.pem",
    "oc_evidence.binarypb",
    # TBD: Remove - we should only export binary protos, not the textproto version.
    "oc_evidence.textproto",
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
    "rekor_public_key.pem",
    "rk_evidence.binarypb",
    "rk_evidence_20240312.binarypb",
    "rk_vcek_milan.der",
    "rk_vcek_milan.pem",
    "vcek_genoa.der",
])
